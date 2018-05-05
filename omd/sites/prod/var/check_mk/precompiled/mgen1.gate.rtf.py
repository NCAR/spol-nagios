#!/usr/bin/python
# encoding: utf-8


import sys

sys.path.pop(0)

import socket
import os
import fnmatch
import time
import re
import signal
import math
import tempfile
import traceback
import subprocess



def reset_global_caches():
    global g_singlehost_checks
    g_singlehost_checks = None  # entries in checks used by just one host
    global g_multihost_checks
    g_multihost_checks  = None  # entries in checks used by more than one host
    global g_ip_lookup_cache
    g_ip_lookup_cache   = None  # permanently cached ipaddresses from ipaddresses.cache

    for cachevar_name in g_global_caches:
        globals()[cachevar_name] = {}

if sys.stdout.isatty():
    tty_red       = '\033[31m'
    tty_green     = '\033[32m'
    tty_yellow    = '\033[33m'
    tty_blue      = '\033[34m'
    tty_magenta   = '\033[35m'
    tty_cyan      = '\033[36m'
    tty_white     = '\033[37m'
    tty_bgblue    = '\033[44m'
    tty_bgmagenta = '\033[45m'
    tty_bgwhite   = '\033[47m'
    tty_bold      = '\033[1m'
    tty_underline = '\033[4m'
    tty_normal    = '\033[0m'
    tty_ok        = tty_green + tty_bold + 'OK' + tty_normal
    def tty(fg=-1, bg=-1, attr=-1):
        if attr >= 0:
            return "\033[3%d;4%d;%dm" % (fg, bg, attr)
        elif bg >= 0:
            return "\033[3%d;4%dm" % (fg, bg)
        elif fg >= 0:
            return "\033[3%dm" % fg
        else:
            return tty_normal
else:
    tty_red       = ''
    tty_green     = ''
    tty_yellow    = ''
    tty_blue      = ''
    tty_magenta   = ''
    tty_cyan      = ''
    tty_white     = ''
    tty_bgblue    = ''
    tty_bgmagenta = ''
    tty_bold      = ''
    tty_underline = ''
    tty_normal    = ''
    tty_ok        = 'OK'
    def tty(fg=-1, bg=-1, attr=-1):
        return ''

def verbose(text):
    if opt_verbose:
        try:
            sys.stdout.write(text)
            sys.stdout.flush()
        except:
            pass # avoid exception on broken pipe (e.g. due to | head)

def vverbose(text):
    if opt_verbose >= 2:
        verbose(text)

def bail_out(reason):
    raise MKBailOut(reason)

def warning(reason):
    stripped = reason.lstrip()
    indent = reason[:len(reason) - len(stripped)]
    sys.stderr.write("%s%s%sWARNING:%s %s\n" % (indent, tty_bold, tty_yellow, tty_normal, stripped))


g_infocache                  = {} # In-memory cache of host info.
g_agent_cache_info           = {} # Information about agent caching
g_agent_already_contacted    = {} # do we have agent data from this host?
g_item_state                 = {} # storing counters of one host
g_hostname                   = "unknown" # Host currently being checked
g_aggregated_service_results = {}   # store results for later submission
g_inactive_timerperiods      = None # Cache for current state of timeperiods
g_last_counter_wrap          = None
nagios_command_pipe          = None # Filedescriptor to open nagios command pipe.
checkresult_file_fd          = None
checkresult_file_path        = None
g_single_oid_hostname        = None
g_single_oid_cache           = {}
g_broken_snmp_hosts          = set([])
g_broken_agent_hosts         = set([])
g_timeout                    = None
g_compiled_regexes           = {}
g_global_caches              = []

g_check_table_cache          = {} # per-host-checktables
g_global_caches.append('g_check_table_cache')
g_nodesof_cache              = {} # Nodes of cluster hosts
g_global_caches.append('g_nodesof_cache')

reset_global_caches()

opt_dont_submit              = False
opt_showplain                = False
opt_showperfdata             = False
opt_use_cachefile            = False
opt_no_tcp                   = False
opt_no_cache                 = False
opt_no_snmp_hosts            = False
opt_use_snmp_walk            = False
opt_cleanup_autochecks       = False
opt_keepalive                = False
opt_cmc_relfilename          = "config"
opt_keepalive_fd             = None
opt_oids                     = []
opt_extra_oids               = []
opt_force                    = False
fake_dns                     = False

core_state_names = ["OK", "WARN", "CRIT", "UNKNOWN"]

state_markers = ["", "(!)", "(!!)", "(?)"]

SKIP  = None
RAISE = False
ZERO  = 0.0


class MKGeneralException(Exception):
    def __init__(self, reason):
        self.reason = reason
    def __str__(self):
        return self.reason

class MKBailOut(Exception):
    def __init__(self, reason):
        self.reason = reason
    def __str__(self):
        return self.reason

class MKCounterWrapped(Exception):
    def __init__(self, reason):
        self.reason = reason
    def __str__(self):
        return self.reason

class MKAgentError(Exception):
    def __init__(self, reason):
        self.reason = reason
    def __str__(self):
        return self.reason

class MKParseFunctionError(Exception):
    def __init__(self, exception_type, exception, backtrace):
        self.exception_type = exception_type
        self.exception = exception
        self.backtrace = backtrace

    def exc_info(self):
        return self.exception_type, self.exception, self.backtrace

    def __str__(self):
        return "%s\n%s" % (self.exception, self.backtrace)

class MKSNMPError(Exception):
    def __init__(self, reason):
        self.reason = reason
    def __str__(self):
        return self.reason

class MKSkipCheck(Exception):
    pass

class MKTimeout(Exception):
    pass


class MKTerminate(Exception):
    pass



def apply_parse_function(info, section_name):
    if info != None and section_name in check_info:
        parse_function = check_info[section_name]["parse_function"]
        if parse_function:
            try:
                global g_check_type, g_checked_item
                g_check_type = section_name
                g_checked_item = None
                return parse_function(info)
            except Exception, e:
                if opt_debug:
                    raise

                raise MKParseFunctionError(*sys.exc_info())

    return info

def get_info_for_check(hostname, ipaddress, section_name, max_cachefile_age=None, ignore_check_interval=False):
    info = apply_parse_function(get_host_info(hostname, ipaddress, section_name, max_cachefile_age, ignore_check_interval), section_name)
    if info != None and section_name in check_info and check_info[section_name]["extra_sections"]:
        info = [ info ]
        for es in check_info[section_name]["extra_sections"]:
            try:
                info.append(apply_parse_function(get_host_info(hostname, ipaddress, es, max_cachefile_age, ignore_check_interval=False), es))
            except:
                info.append(None)
    return info





def get_host_info(hostname, ipaddress, checkname, max_cachefile_age=None, ignore_check_interval=False):
    add_nodeinfo = check_info.get(checkname, {}).get("node_info", False)

    nodes = nodes_of(hostname)
    if nodes != None:
        info = []
        at_least_one_without_exception = False
        exception_texts = []
        set_use_cachefile()
        is_snmp_error = False
        for node in nodes:
            try:
                ipaddress = lookup_ip_address(node)
                new_info = get_realhost_info(node, ipaddress, checkname,
                               max_cachefile_age == None and cluster_max_cachefile_age or max_cachefile_age,
                               ignore_check_interval=True)
                if new_info != None:
                    if add_nodeinfo:
                        new_info = [ [node] + line for line in new_info ]
                    info += new_info
                    at_least_one_without_exception = True
            except MKSkipCheck:
                at_least_one_without_exception = True
            except MKAgentError, e:
                if str(e) != "": # only first error contains text
                    exception_texts.append(str(e))
                g_broken_agent_hosts.add(node)
            except MKSNMPError, e:
                if str(e) != "": # only first error contains text
                    exception_texts.append(str(e))
                g_broken_snmp_hosts.add(node)
                is_snmp_error = True
        if not at_least_one_without_exception:
            if is_snmp_error:
                raise MKSNMPError(", ".join(exception_texts))
            else:
                raise MKAgentError(", ".join(exception_texts))

    else:
        info = get_realhost_info(hostname, ipaddress, checkname,
                      max_cachefile_age == None and check_max_cachefile_age or max_cachefile_age,
                      ignore_check_interval)
        if info != None and add_nodeinfo:
            if clusters_of(hostname):
                add_host = hostname
            else:
                add_host = None
            info = [ [add_host] + line for line in info ]

    return info


def get_realhost_info(hostname, ipaddress, check_type, max_cache_age,
                      ignore_check_interval=False, use_snmpwalk_cache=True):

    info = get_cached_hostinfo(hostname)
    if info and info.has_key(check_type):
        return info[check_type]

    cache_relpath = hostname + "." + check_type

    info_type = check_type.split(".")[0]
    if info_type in snmp_info:
        oid_info = snmp_info[info_type]
    elif info_type in inv_info:
        oid_info = inv_info[info_type].get("snmp_info")
    else:
        oid_info = None

    if oid_info:
        cache_path = tcp_cache_dir + "/" + cache_relpath

        check_interval = check_interval_of(hostname, check_type)
        if not ignore_check_interval \
           and not opt_dont_submit \
           and check_interval is not None and os.path.exists(cache_path) \
           and cachefile_age(cache_path) < check_interval * 60:
            raise MKSkipCheck()

        try:
            content = read_cache_file(cache_relpath, max_cache_age)
        except:
            if simulation_mode and not opt_no_cache:
                return # Simply ignore missing SNMP cache files
            raise

        if content:
            return eval(content)

        if hostname in g_broken_snmp_hosts:
            raise MKSNMPError("")

        if type(oid_info) == list:
            table = [ get_snmp_table(hostname, ipaddress, check_type, entry, use_snmpwalk_cache) for entry in oid_info ]
            if None in table:
                table = None
        else:
            table = get_snmp_table(hostname, ipaddress, check_type, oid_info, use_snmpwalk_cache)
        store_cached_checkinfo(hostname, check_type, table)
        if not opt_dont_submit:
            write_cache_file(cache_relpath, repr(table) + "\n")
        return table


    if g_agent_already_contacted.has_key(hostname):
        raise MKAgentError("")

    g_agent_already_contacted[hostname] = True
    store_cached_hostinfo(hostname, []) # leave emtpy info in case of error

    piggy_output = get_piggyback_info(hostname) + get_piggyback_info(ipaddress)

    output = ""
    agent_failed_exc = None
    if is_tcp_host(hostname):
        try:
            output = get_agent_info(hostname, ipaddress, max_cache_age)
        except MKTimeout:
            raise

        except Exception, e:
            agent_failed_exc = e
            remove_piggyback_info_from(hostname)

            if not piggy_output:
                raise
            elif opt_debug:
                raise

    output += piggy_output

    if len(output) == 0 and is_tcp_host(hostname):
        raise MKAgentError("Empty output from agent")
    elif len(output) == 0:
        return
    elif len(output) < 16:
        raise MKAgentError("Too short output from agent: '%s'" % output)

    info, piggybacked, persisted, agent_cache_info = parse_info(output.split("\n"), hostname)
    g_agent_cache_info.setdefault(hostname, {}).update(agent_cache_info)
    store_piggyback_info(hostname, piggybacked)
    store_persisted_info(hostname, persisted)
    store_cached_hostinfo(hostname, info)

    add_persisted_info(hostname, info)

    if check_type not in info:
        if agent_failed_exc:
            raise MKAgentError("Cannot get information from agent (%s), processing only piggyback data." % agent_failed_exc)
        else:
            return []

    return info[check_type] # return only data for specified check

def store_persisted_info(hostname, persisted):
    dirname = var_dir + "/persisted/"
    if persisted:
        if not os.path.exists(dirname):
            os.makedirs(dirname)

        file_path = "%s/%s" % (dirname, hostname)
        file("%s.#new" % file_path, "w").write("%r\n" % persisted)
        os.rename("%s.#new" % file_path, file_path)

        verbose("Persisted sections %s.\n" % ", ".join(persisted.keys()))


def add_persisted_info(hostname, info):
    file_path = var_dir + "/persisted/" + hostname
    try:
        persisted = eval(file(file_path).read())
    except:
        return

    now = time.time()
    modified = False
    for section, entry in persisted.items():
        if len(entry) == 2:
            persisted_from = None
            persisted_until, persisted_section = entry
        else:
            persisted_from, persisted_until, persisted_section = entry
            g_agent_cache_info[hostname][section] = (persisted_from, persisted_until - persisted_from)

        if now < persisted_until or opt_force:
            if section not in info:
                info[section] = persisted_section
                vverbose("Added persisted section %s.\n" % section)
        else:
            verbose("Persisted section %s is outdated by %d seconds. Deleting it.\n" % (
                    section, now - persisted_until))
            del persisted[section]
            modified = True

    if not persisted:
        try:
            os.remove(file_path)
        except OSError:
            pass
    elif modified:
        store_persisted_info(hostname, persisted)


def get_piggyback_files(hostname):
    files = []
    dir = tmp_dir + "/piggyback/" + hostname
    if os.path.exists(dir):
        for sourcehost in os.listdir(dir):
            if sourcehost not in ['.', '..'] \
               and not sourcehost.startswith(".new."):
                file_path = dir + "/" + sourcehost

                if cachefile_age(file_path) > piggyback_max_cachefile_age:
                    verbose("Piggyback file %s is outdated by %d seconds. Deleting it.\n" %
                        (file_path, cachefile_age(file_path) - piggyback_max_cachefile_age))
                    os.remove(file_path)
                    continue

                files.append((sourcehost, file_path))
    return files


def has_piggyback_info(hostname):
    return get_piggyback_files(hostname) != []


def get_piggyback_info(hostname):
    output = ""
    if not hostname:
        return output
    for sourcehost, file_path in get_piggyback_files(hostname):
        verbose("Using piggyback information from host %s.\n" % sourcehost)
        output += file(file_path).read()
    return output


def store_piggyback_info(sourcehost, piggybacked):
    piggyback_path = tmp_dir + "/piggyback/"
    for backedhost, lines in piggybacked.items():
        verbose("Storing piggyback data for %s.\n" % backedhost)
        dir = piggyback_path + backedhost
        if not os.path.exists(dir):
            os.makedirs(dir)
        out = file(dir + "/.new." + sourcehost, "w")
        for line in lines:
            out.write("%s\n" % line)
        os.rename(dir + "/.new." + sourcehost, dir + "/" + sourcehost)

    remove_piggyback_info_from(sourcehost, keep=piggybacked.keys())


def remove_piggyback_info_from(sourcehost, keep=[]):
    removed = 0
    piggyback_path = tmp_dir + "/piggyback/"
    if not os.path.exists(piggyback_path):
        return # Nothing to do

    for backedhost in os.listdir(piggyback_path):
        if backedhost not in ['.', '..'] and backedhost not in keep:
            path = piggyback_path + backedhost + "/" + sourcehost
            if os.path.exists(path):
                verbose("Removing stale piggyback file %s\n" % path)
                os.remove(path)
                removed += 1

            try:
                os.rmdir(piggyback_path + backedhost)
            except:
                pass
    return removed


def translate_piggyback_host(sourcehost, backedhost):
    translation = get_piggyback_translation(sourcehost)
    return do_hostname_translation(translation, backedhost)


def do_hostname_translation(translation, hostname):
    caseconf = translation.get("case")
    if caseconf == "upper":
        hostname = hostname.upper()
    elif caseconf == "lower":
        hostname = hostname.lower()

    if translation.get("drop_domain") and not hostname[0].isdigit():
        hostname = hostname.split(".", 1)[0]

    hostname = decode_incoming_string(hostname)

    if "regex" in translation:
        expr, subst = translation.get("regex")
        if not expr.endswith('$'):
            expr += '$'
        rcomp = regex(expr)
        mo = rcomp.match(hostname)
        if mo:
            hostname = subst
            for nr, text in enumerate(mo.groups("")):
                hostname = hostname.replace("\\%d" % (nr+1), text)

    for from_host, to_host in translation.get("mapping", []):
        if from_host == hostname:
            hostname = to_host
            break

    return hostname.encode('utf-8') # change back to UTF-8 encoded string


def read_cache_file(relpath, max_cache_age):
    cachefile = tcp_cache_dir + "/" + relpath
    if os.path.exists(cachefile) and (
        (opt_use_cachefile and ( not opt_no_cache ) )
        or (simulation_mode and not opt_no_cache) ):
        if cachefile_age(cachefile) <= max_cache_age or simulation_mode:
            f = open(cachefile, "r")
            result = f.read(10000000)
            f.close()
            if len(result) > 0:
                verbose("Using data from cachefile %s.\n" % cachefile)
                return result
        else:
            vverbose("Skipping cache file %s: Too old "
                             "(age is %d sec, allowed is %s sec)\n" %
                   (cachefile, cachefile_age(cachefile), max_cache_age))

    if simulation_mode and not opt_no_cache:
        raise MKAgentError("Simulation mode and no cachefile present.")

    if opt_no_tcp:
        raise MKAgentError("Host is unreachable, no usable cache file present")


def write_cache_file(relpath, output):
    cachefile = tcp_cache_dir + "/" + relpath
    if not os.path.exists(tcp_cache_dir):
        try:
            os.makedirs(tcp_cache_dir)
        except Exception, e:
            raise MKGeneralException("Cannot create directory %s: %s" % (tcp_cache_dir, e))
    try:
        if not i_am_root():
            f = open(cachefile, "w+")
            f.write(output)
            f.close()
    except Exception, e:
        raise MKGeneralException("Cannot write cache file %s: %s" % (cachefile, e))


def get_agent_info(hostname, ipaddress, max_cache_age):
    if ipaddress in [ "0.0.0.0", "::" ]:
        raise MKAgentError("Failed to lookup IP address and no explicit IP address configured")

    output = read_cache_file(hostname, max_cache_age)
    if not output:
        if hostname in g_broken_agent_hosts:
            raise MKAgentError("")

        commandline = get_datasource_program(hostname, ipaddress)
        if commandline:
            output = get_agent_info_program(commandline)
        else:
            output = get_agent_info_tcp(hostname, ipaddress)

        write_cache_file(hostname, output)

    if agent_simulator:
        output = agent_simulator_process(output)

    return output

def get_agent_info_program(commandline):
    exepath = commandline.split()[0] # for error message, hide options!

    vverbose("Calling external program %s\n" % commandline)
    p = None
    try:
        if monitoring_core == "cmc":
            p = subprocess.Popen(commandline, shell=True, stdin=open(os.devnull),
                                 stdout=subprocess.PIPE, stderr = subprocess.PIPE,
                                 preexec_fn=os.setsid, close_fds=True)
        else:
            p = subprocess.Popen(commandline, shell=True, stdin=open(os.devnull),
                                 stdout=subprocess.PIPE, stderr = subprocess.PIPE,
                                 close_fds=True)
        stdout, stderr = p.communicate()
        exitstatus = p.returncode
        p.stdout.close()
        p.stderr.close()
    except MKTimeout:
        if p:
            os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            p.stdout.close()
            p.stderr.close()
        raise
    except Exception, e:
        if p:
            p.stdout.close()
            p.stderr.close()
        raise MKAgentError("Could not execute '%s': %s" % (exepath, e))

    if exitstatus:
        if exitstatus == 127:
            raise MKAgentError("Program '%s' not found (exit code 127)" % exepath)
        else:
            raise MKAgentError("Agent exited with code %d: %s" % (exitstatus, stderr))
    return stdout

def get_agent_info_tcp(hostname, ipaddress, port = None):
    if not ipaddress:
        raise MKGeneralException("Cannot contact agent: host '%s' has no IP address." % hostname)

    if port is None:
        port = agent_port_of(hostname)

    try:
        s = socket.socket(is_ipv6_primary(hostname) and socket.AF_INET6 or socket.AF_INET,
                          socket.SOCK_STREAM)
        try:
            s.settimeout(tcp_connect_timeout)
        except:
            pass # some old Python versions lack settimeout(). Better ignore than fail
        vverbose("Connecting via TCP to %s:%d.\n" % (ipaddress, port))
        s.connect((ipaddress, port))
        try:
            s.setblocking(1)
        except:
            pass
        output = ""
        try:
            while True:
                out = s.recv(4096, socket.MSG_WAITALL)
                if out and len(out) > 0:
                    output += out
                else:
                    break
        except Exception, e:
            s.close()
            raise

        s.close()
        if len(output) == 0: # may be caused by xinetd not allowing our address
            raise MKAgentError("Empty output from agent at TCP port %d" % port)
        return output
    except MKAgentError, e:
        raise
    except MKTimeout:
        raise
    except Exception, e:
        raise MKAgentError("Cannot get data from TCP port %s:%d: %s" %
                           (ipaddress, port, e))


def get_cached_hostinfo(hostname):
    return g_infocache.get(hostname, None)

def store_cached_hostinfo(hostname, info):
    oldinfo = get_cached_hostinfo(hostname)
    if oldinfo:
        oldinfo.update(info)
        g_infocache[hostname] = oldinfo
    else:
        g_infocache[hostname] = info

def store_cached_checkinfo(hostname, checkname, table):
    info = get_cached_hostinfo(hostname)
    if info:
        info[checkname] = table
    else:
        g_infocache[hostname] = { checkname: table }


def parse_info(lines, hostname):
    info = {}
    piggybacked = {} # unparsed info for other hosts
    persist = {} # handle sections with option persist(...)
    host = None
    section = []
    section_options = {}
    agent_cache_info = {}
    separator = None
    encoding  = None
    to_unicode = False
    for line in lines:
        line = line.rstrip("\r")
        stripped_line = line.strip()
        if stripped_line[:4] == '<<<<' and stripped_line[-4:] == '>>>>':
            host = stripped_line[4:-4]
            if not host:
                host = None
            else:
                host = translate_piggyback_host(hostname, host)
                if host == hostname:
                    host = None # unpiggybacked "normal" host
        elif host: # processing data for an other host
            piggybacked.setdefault(host, []).append(line)

        elif stripped_line[:3] == '<<<' and stripped_line[-3:] == '>>>':
            section_header = stripped_line[3:-3]
            headerparts = section_header.split(":")
            section_name = headerparts[0]
            section_options = {}
            for o in headerparts[1:]:
                opt_parts = o.split("(")
                opt_name = opt_parts[0]
                if len(opt_parts) > 1:
                    opt_args = opt_parts[1][:-1]
                else:
                    opt_args = None
                section_options[opt_name] = opt_args

            section = info.get(section_name, None)
            if section == None: # section appears in output for the first time
                section = []
                info[section_name] = section
            try:
                separator = chr(int(section_options["sep"]))
            except:
                separator = None

            if "persist" in section_options:
                until = int(section_options["persist"])
                cached_at = int(time.time()) # Estimate age of the data
                cache_interval = int(until - cached_at)
                agent_cache_info[section_name] = (cached_at, cache_interval)
                persist[section_name] = ( cached_at, until, section )

            if "cached" in section_options:
                agent_cache_info[section_name] = tuple(map(int, section_options["cached"].split(",")))

            encoding = section_options.get("encoding")

        elif stripped_line != '':
            if "nostrip" not in section_options:
                line = stripped_line

            if encoding:
                line = decode_incoming_string(line, encoding)
            else:
                line = decode_incoming_string(line)

            section.append(line.split(separator))

    return info, piggybacked, persist, agent_cache_info


def decode_incoming_string(s, encoding="utf-8"):
    try:
        return s.decode(encoding)
    except:
        return s.decode(fallback_agent_output_encoding)


def cachefile_age(filename):
    try:
        return time.time() - os.stat(filename)[8]
    except Exception, e:
        raise MKGeneralException("Cannot determine age of cache file %s: %s" \
                                 % (filename, e))
        return -1



def load_item_state(hostname):
    global g_item_state
    filename = counters_directory + "/" + hostname
    try:
        g_item_state = eval(file(filename).read())
    except:
        g_item_state = {}


def save_item_state(hostname):
    if not opt_dont_submit and not i_am_root(): # never writer counters as root
        filename = counters_directory + "/" + hostname
        try:
            if not os.path.exists(counters_directory):
                os.makedirs(counters_directory)
            file(filename, "w").write("%r\n" % g_item_state)
        except Exception, e:
            import pwd
            username = pwd.getpwuid(os.getuid())[0]
            raise MKGeneralException("User %s cannot write to %s: %s" % (username, filename, e))


def set_item_state(user_key, state):
    g_item_state[unique_item_state_key(user_key)] = state


def get_item_state(user_key, default=None):
    return g_item_state.get(unique_item_state_key(user_key), default)


def clear_item_state(user_key):
    key = unique_item_state_key(user_key)
    if key in g_item_state:
        del g_item_state[key]


def unique_item_state_key(user_key):
    return (g_check_type, g_checked_item, user_key)


def get_rate(user_key, this_time, this_val, allow_negative=False, onwrap=SKIP, is_rate=False):
    try:
        timedif, rate = get_counter(user_key, this_time, this_val, allow_negative, is_rate)
        return rate
    except MKCounterWrapped, e:
        if onwrap is RAISE:
            raise
        elif onwrap is SKIP:
            global g_last_counter_wrap
            g_last_counter_wrap = e
            return 0.0
        else:
            return onwrap


def get_counter(countername, this_time, this_val, allow_negative=False, is_rate=False):
    old_state = get_item_state(countername, None)
    set_item_state(countername, (this_time, this_val))

    if old_state is None:
        if opt_dont_submit:
            return 1.0, 0.0
        raise MKCounterWrapped('Counter initialization')

    last_time, last_val = old_state
    timedif = this_time - last_time
    if timedif <= 0: # do not update counter
        if opt_dont_submit:
            return 1.0, 0.0
        raise MKCounterWrapped('No time difference')

    if not is_rate:
        valuedif = this_val - last_val
    else:
        valuedif = this_val

    if valuedif < 0 and not allow_negative:
        if opt_dont_submit:
            return 1.0, 0.0
        raise MKCounterWrapped('Value overflow')

    per_sec = float(valuedif) / timedif
    return timedif, per_sec


def reset_wrapped_counters():
    global g_last_counter_wrap
    g_last_counter_wrap = None


def last_counter_wrap():
    return g_last_counter_wrap


def get_average(itemname, this_time, this_val, backlog_minutes, initialize_zero = True):
    old_state = get_item_state(itemname, None)

    if old_state is None:
        if initialize_zero:
            this_val = 0
        set_item_state(itemname, (this_time, this_val))
        return this_val # avoid time diff of 0.0 -> avoid division by zero

    last_time, last_val = old_state
    timedif = this_time - last_time

    if timedif < 0:
        timedif = 0

    try:
        percentile = 0.50

        weight_per_minute = (1 - percentile) ** (1.0 / backlog_minutes)

        weight = weight_per_minute ** (timedif / 60.0)

    except OverflowError:
        weight = 0

    new_val = last_val * weight + this_val * (1 - weight)

    set_item_state(itemname, (this_time, new_val))
    return new_val





def do_check(hostname, ipaddress, only_check_types = None):
    verbose("Check_mk version %s\n" % check_mk_version)

    start_time = time.time()

    expected_version = agent_target_version(hostname)

    exit_spec = exit_code_spec(hostname)

    try:
        load_item_state(hostname)
        agent_version, num_success, error_sections, problems = \
            do_all_checks_on_host(hostname, ipaddress, only_check_types)

        num_errors = len(error_sections)
        save_item_state(hostname)
        if problems:
            output = "%s, " % problems
            status = exit_spec.get("connection", 2)
        elif num_errors > 0 and num_success > 0:
            output = "Missing agent sections: %s - " % ", ".join(error_sections)
            status = exit_spec.get("missing_sections", 1)
        elif num_errors > 0:
            output = "Got no information from host, "
            status = exit_spec.get("empty_output", 2)
        elif expected_version and agent_version \
             and not is_expected_agent_version(agent_version, expected_version):
            if type(expected_version) == tuple and expected_version[0] == 'at_least':
                expected = 'at least'
                if 'daily_build' in expected_version[1]:
                    expected += ' build %s' % expected_version[1]['daily_build']
                if 'release' in expected_version[1]:
                    if 'daily_build' in expected_version[1]:
                        expected += ' or'
                    expected += ' release %s' % expected_version[1]['release']
            else:
                expected = expected_version
            output = "unexpected agent version %s (should be %s), " % (agent_version, expected)
            status = exit_spec.get("wrong_version", 1)
        elif agent_min_version and agent_version < agent_min_version:
            output = "old plugin version %s (should be at least %s), " % (agent_version, agent_min_version)
            status = exit_spec.get("wrong_version", 1)
        else:
            output = ""
            if not is_cluster(hostname) and agent_version != None:
                output += "Agent version %s, " % agent_version
            status = 0

    except MKTimeout:
        raise

    except MKGeneralException, e:
        if opt_debug:
            raise
        output = "%s, " % e
        status = exit_spec.get("exception", 3)

    if aggregate_check_mk:
        try:
            submit_check_mk_aggregation(hostname, status, output)
        except:
            if opt_debug:
                raise

    if checkresult_file_fd != None:
        close_checkresult_file()

    run_time = time.time() - start_time
    if check_mk_perfdata_with_times:
        if opt_keepalive:
            times = get_keepalive_times()
        else:
            times = os.times()

        output += "execution time %.1f sec|execution_time=%.3f user_time=%.3f "\
                  "system_time=%.3f children_user_time=%.3f children_system_time=%.3f\n" %\
                (run_time, run_time, times[0], times[1], times[2], times[3])
    else:
        output += "execution time %.1f sec|execution_time=%.3f\n" % (run_time, run_time)

    if record_inline_snmp_stats and is_inline_snmp_host(hostname):
        save_snmp_stats()

    if opt_keepalive:
        add_keepalive_active_check_result(hostname, output)
        verbose(output)
    else:
        sys.stdout.write(core_state_names[status] + " - " + output.encode('utf-8'))

    return status


def is_expected_agent_version(agent_version, expected_version):
    try:
        if agent_version in [ '(unknown)', None, 'None' ]:
            return False

        if type(expected_version) == str and expected_version != agent_version:
            return False

        elif type(expected_version) == tuple and expected_version[0] == 'at_least':
            spec = expected_version[1]
            if is_daily_build_version(agent_version) and 'daily_build' in spec:
                expected = int(spec['daily_build'].replace('.', ''))

                branch = branch_of_daily_build(agent_version)
                if branch == "master":
                    agent = int(agent_version.replace('.', ''))

                else: # branch build (e.g. 1.2.4-2014.06.01)
                    agent = int(agent_version.split('-')[1].replace('.', ''))

                if agent < expected:
                    return False

            elif 'release' in spec:
                if parse_check_mk_version(agent_version) < parse_check_mk_version(spec['release']):
                    return False

        return True
    except Exception, e:
        if opt_debug:
            raise
        raise MKGeneralException("Unable to check agent version (Agent: %s Expected: %s, Error: %s)" %
                (agent_version, expected_version, e))


def is_daily_build_version(v):
    return len(v) == 10 or '-' in v


def branch_of_daily_build(v):
    if len(v) == 10:
        return "master"
    else:
        return v.split('-')[0]


def parse_check_mk_version(v):
    def extract_number(s):
        number = ''
        for i, c in enumerate(s):
            try:
                int(c)
                number += c
            except ValueError:
                s = s[i:]
                return number and int(number) or 0, s
        return number and int(number) or 0, ''

    parts = v.split('.')
    while len(parts) < 3:
        parts.append("0")

    major, minor, rest = parts
    sub, rest = extract_number(rest)

    if not rest:
        val = 50000
    elif rest[0] == 'p':
        num, rest = extract_number(rest[1:])
        val = 50000 + num
    elif rest[0] == 'i':
        num, rest = extract_number(rest[1:])
        val = 10000 + num*100

        if rest and rest[0] == 'p':
            num, rest = extract_number(rest[1:])
            val += num
    elif rest[0] == 'b':
        num, rest = extract_number(rest[1:])
        val = 20000 + num*100

    return int('%02d%02d%02d%05d' % (int(major), int(minor), sub, val))


def do_all_checks_on_host(hostname, ipaddress, only_check_types = None, fetch_agent_version = True):
    global g_aggregated_service_results
    g_aggregated_service_results = {}
    global g_hostname
    g_hostname = hostname
    num_success = 0
    error_sections = set([])
    check_table = get_precompiled_check_table(hostname, remove_duplicates=True,
                                    world=opt_keepalive and "active" or "config")
    problems = []

    parsed_infos = {} # temporary cache for section infos, maybe parsed

    for checkname, item, params, description, aggrname in check_table:
        if only_check_types != None and checkname not in only_check_types:
            continue

        global g_service_description, g_check_type, g_checked_item
        g_service_description = description
        g_check_type = checkname
        g_checked_item = item

        period = check_period_of(hostname, description)
        if period and not check_timeperiod(period):
            verbose("Skipping service %s: currently not in timeperiod %s.\n" % (description, period))
            continue

        elif period:
            vverbose("Service %s: timeperiod %s is currently active.\n" % (description, period))

        infotype = checkname.split('.')[0]
        try:
            if infotype in parsed_infos:
                info = parsed_infos[infotype]
            else:
                info = get_info_for_check(hostname, ipaddress, infotype)
                parsed_infos[infotype] = info

        except MKSkipCheck, e:
            continue

        except MKSNMPError, e:
            if str(e):
                problems.append(str(e))
            error_sections.add(infotype)
            g_broken_snmp_hosts.add(hostname)
            continue

        except MKAgentError, e:
            if str(e):
                problems.append(str(e))
            error_sections.add(infotype)
            g_broken_agent_hosts.add(hostname)
            continue

        except MKParseFunctionError, e:
            info = e

        if info == [] and check_uses_snmp(checkname) \
           and not check_info[checkname]["handle_empty_info"]:
            error_sections.add(infotype)
            continue

        if info or info in [ [], {} ]:
            num_success += 1
            try:
                check_function = check_info[checkname]["check_function"]
            except:
                check_function = check_unimplemented

            try:
                dont_submit = False

                reset_wrapped_counters()

                if isinstance(info, MKParseFunctionError):
                    x = info.exc_info()
                    raise x[0], x[1], x[2] # re-raise the original exception to not destory the trace

                result = sanitize_check_result(check_function(item, params, info), check_uses_snmp(checkname))
                if last_counter_wrap():
                    raise last_counter_wrap()


            except MKCounterWrapped, e:
                verbose("%-20s PEND - Cannot compute check result: %s\n" % (description, e))
                dont_submit = True

            except Exception, e:
                if opt_debug:
                    raise
                result = 3, create_crash_dump(hostname, checkname, item, params, description, info), []

            if not dont_submit:
                oldest_cached_at = None
                largest_interval = None

                def minn(a, b):
                    if a == None:
                        return b
                    elif b == None:
                        return a
                    return min(a,b)

                for section_entries in g_agent_cache_info.values():
                    if infotype in section_entries:
                        cached_at, cache_interval = section_entries[infotype]
                        oldest_cached_at = minn(oldest_cached_at, cached_at)
                        largest_interval = max(largest_interval, cache_interval)

                submit_check_result(hostname, description, result, aggrname,
                                    cached_at=oldest_cached_at, cache_interval=largest_interval)
        else:
            error_sections.add(infotype)

    submit_aggregated_results(hostname)

    if fetch_agent_version:
        try:
            if is_tcp_host(hostname):
                version_info = get_info_for_check(hostname, ipaddress, 'check_mk')
                agent_version = version_info[0][1]
            else:
                agent_version = None
        except MKAgentError, e:
            g_broken_agent_hosts.add(hostname)
            agent_version = "(unknown)"
        except:
            agent_version = "(unknown)"
    else:
        agent_version = None

    error_sections = list(error_sections)
    error_sections.sort()

    return agent_version, num_success, error_sections, ", ".join(problems)


def create_crash_dump(hostname, check_type, item, params, description, info):
    text = "check failed - please submit a crash report!"
    try:
        crash_dir = var_dir + "/crashed_checks/" + hostname + "/" + description.replace("/", "\\")
        prepare_crash_dump_directory(crash_dir)

        create_crash_dump_info_file(crash_dir, hostname, check_type, item, params, description, info, text)
        if check_uses_snmp(check_type):
            write_crash_dump_snmp_info(crash_dir, hostname, check_type)
        else:
            write_crash_dump_agent_output(crash_dir, hostname)

        text += "\n" + "Crash dump:\n" + pack_crash_dump(crash_dir) + "\n"
    except:
        if opt_debug:
            raise

    return text


def prepare_crash_dump_directory(crash_dir):
    if not os.path.exists(crash_dir):
        os.makedirs(crash_dir)
    for f in os.listdir(crash_dir):
        try:
            os.unlink(crash_dir + "/" + f)
        except OSError:
            pass


def is_manual_check(hostname, check_type, item):
    if not "get_check_table" in globals():
        return None

    manual_checks = get_check_table(hostname, remove_duplicates=True,
                                    world=opt_keepalive and "active" or "config",
                                    skip_autochecks=True)
    return (check_type, item) in manual_checks


def format_var_for_export(val, maxdepth=4, maxsize=1024*1024):
    if maxdepth == 0:
        return "Max recursion depth reached"

    if isinstance(val, dict):
        val = val.copy()
        for item_key, item_val in val.items():
            val[item_key] = format_var_for_export(item_val, maxdepth-1)

    elif isinstance(val, list):
        val = val[:]
        for index, item in enumerate(val):
            val[index] = format_var_for_export(item, maxdepth-1)

    elif isinstance(val, tuple):
        new_val = ()
        for item in val:
            new_val += (format_var_for_export(item, maxdepth-1),)
        val = new_val

    if type(val) in (str, unicode):
        size = len(val)
        if size > maxsize:
            val = val[:maxsize] + "... (%d bytes stripped)" % (size - maxsize)

    return val


def get_local_vars_of_last_exception():
    local_vars = {}
    import inspect, base64, pprint
    for key, val in inspect.trace()[-1][0].f_locals.items():
        local_vars[key] = format_var_for_export(val)

    return base64.b64encode(format_var_for_export(pprint.pformat(local_vars), maxsize=5*1024*1024))


def create_crash_dump_info_file(crash_dir, hostname, check_type, item, params, description, info, text):
    exc_type, exc_value, exc_traceback = sys.exc_info()

    crash_info = {
        "crash_type"    : "check",
        "time"          : time.time(),
        "os"            : get_os_info(),
        "version"       : check_mk_version,
        "python_version": sys.version,
        "exc_type"      : exc_type.__name__,
        "exc_value"     : "%s" % exc_value,
        "exc_traceback" : traceback.extract_tb(exc_traceback),
        "local_vars"    : get_local_vars_of_last_exception(),
        "details"    : {
            "check_output"  : text,
            "host"          : hostname,
            "is_cluster"    : is_cluster(hostname),
            "description"   : description,
            "check_type"    : check_type,
            "item"          : item,
            "params"        : params,
            "uses_snmp"     : check_uses_snmp(check_type),
            "inline_snmp"   : is_inline_snmp_host(hostname),
            "manual_check"  : is_manual_check(hostname, check_type, item),
        },
    }

    try:
        import simplejson as json
    except ImportError:
        import json


    class RobustJSONEncoder(json.JSONEncoder):
        def default(self, o):
            return "%s" % o

    file(crash_dir+"/crash.info", "w").write(json.dumps(crash_info, cls=RobustJSONEncoder)+"\n")


def get_os_info():
    if omd_root:
        return file(omd_root+"/share/omd/distro.info").readline().split("=", 1)[1].strip()
    elif os.path.exists("/etc/redhat-release"):
        return file("/etc/redhat-release").readline().strip()
    elif os.path.exists("/etc/SuSE-release"):
        return file("/etc/SuSE-release").readline().strip()
    else:
        info = {}
        for f in [ "/etc/os-release", "/etc/lsb-release" ]:
            if os.path.exists(f):
                for line in file(f).readlines():
                    if "=" in line:
                        k, v = line.split("=", 1)
                        info[k.strip()] = v.strip()
                break

        if info:
            return info
        else:
            return "UNKNOWN"


def write_crash_dump_snmp_info(crash_dir, hostname, check_type):
    cachefile = tcp_cache_dir + "/" + hostname + "." + check_type.split(".")[0]
    if os.path.exists(cachefile):
        file(crash_dir + "/snmp_info", "w").write(file(cachefile).read())


def write_crash_dump_agent_output(crash_dir, hostname):
    if "get_rtc_package" in globals():
        file(crash_dir + "/agent_output", "w").write(get_rtc_package())
    else:
        cachefile = tcp_cache_dir + "/" + hostname
        if os.path.exists(cachefile):
            file(crash_dir + "/agent_output", "w").write(file(cachefile).read())


def pack_crash_dump(crash_dir):
    import base64
    tarcontent = os.popen("cd %s ; tar czf - *" % quote_shell_string(crash_dir)).read()
    return base64.b64encode(tarcontent)


def check_unimplemented(checkname, params, info):
    return (3, 'UNKNOWN - Check not implemented')

def convert_check_info():
    for check_type, info in check_info.items():
        basename = check_type.split(".")[0]

        if type(info) != dict:
            check_function, service_description, has_perfdata, inventory_function = info
            if inventory_function == no_discovery_possible:
                inventory_function = None

            check_info[check_type] = {
                "check_function"          : check_function,
                "service_description"     : service_description,
                "has_perfdata"            : not not has_perfdata,
                "inventory_function"      : inventory_function,
                "group"                   : checkgroup_of.get(check_type, check_type),
                "snmp_info"               : snmp_info.get(check_type),
                "snmp_scan_function"      :
                    snmp_scan_functions.get(check_type,
                        snmp_scan_functions.get(basename)),
                "handle_empty_info"       : False,
                "handle_real_time_checks" : False,
                "default_levels_variable" : check_default_levels.get(check_type),
                "node_info"               : False,
                "parse_function"          : None,
                "extra_sections"          : [],
            }
        else:
            info.setdefault("inventory_function", None)
            info.setdefault("parse_function", None)
            info.setdefault("group", None)
            info.setdefault("snmp_info", None)
            info.setdefault("snmp_scan_function", None)
            info.setdefault("handle_empty_info", False)
            info.setdefault("handle_real_time_checks", False)
            info.setdefault("default_levels_variable", None)
            info.setdefault("node_info", False)
            info.setdefault("extra_sections", [])

            check_includes.setdefault(basename, [])
            check_includes[basename] += info.get("includes", [])

    for check_type, info in check_info.iteritems():
        if "." in check_type:
            base_check = check_type.split(".")[0]
            if base_check not in check_info:
                if info["node_info"]:
                    raise MKGeneralException("Invalid check implementation: node_info for %s is True, but base check %s not defined" %
                        (check_type, base_check))
            elif check_info[base_check]["node_info"] != info["node_info"]:
               raise MKGeneralException("Invalid check implementation: node_info for %s and %s are different." % (
                   (base_check, check_type)))

    for check_type, info in check_info.iteritems():
        basename = check_type.split(".")[0]
        if info["snmp_info"] and basename not in snmp_info:
            snmp_info[basename] = info["snmp_info"]
        if info["snmp_scan_function"] and basename not in snmp_scan_functions:
            snmp_scan_functions[basename] = info["snmp_scan_function"]


def sanitize_check_result(result, is_snmp):
    if type(result) == tuple:
        return sanitize_tuple_check_result(result)

    elif result == None:
        return item_not_found(is_snmp)

    else:
        return sanitize_yield_check_result(result, is_snmp)


def sanitize_yield_check_result(result, is_snmp):
    subresults = list(result)

    if not subresults:
        return item_not_found(is_snmp)

    if len(subresults) == 1:
        state, infotext, perfdata = sanitize_tuple_check_result(subresults[0], allow_missing_infotext=True)
        if infotext == None:
            return state, u"", perfdata
        else:
            return state, infotext, perfdata

    else:
        perfdata = []
        infotexts = []
        status = 0

        for subresult in subresults:
            st, text, perf = sanitize_tuple_check_result(subresult, allow_missing_infotext=True)

            if text != None:
                infotexts.append(text + ["", "(!)", "(!!)", "(?)"][st])
                status = worst_monitoring_state(st, status)

            if perf != None:
                perfdata += subresult[2]

        return status, ", ".join(infotexts), perfdata


def item_not_found(is_snmp):
    if is_snmp:
        return 3, "Item not found in SNMP data", []
    else:
        return 3, "Item not found in agent output", []


def sanitize_tuple_check_result(result, allow_missing_infotext=False):
    if len(result) >= 3:
        state, infotext, perfdata = result[:3]
    else:
        state, infotext = result
        perfdata = None

    infotext = sanitize_check_result_infotext(infotext, allow_missing_infotext)

    return state, infotext, perfdata


def sanitize_check_result_infotext(infotext, allow_missing_infotext):
    if infotext == None and not allow_missing_infotext:
        raise MKGeneralException("Invalid infotext from check: \"None\"")

    if type(infotext) == str:
        return infotext.decode('utf-8')
    else:
        return infotext


def open_checkresult_file():
    global checkresult_file_fd
    global checkresult_file_path
    if checkresult_file_fd == None:
        try:
            checkresult_file_fd, checkresult_file_path = \
                tempfile.mkstemp('', 'c', check_result_path)
        except Exception, e:
            raise MKGeneralException("Cannot create check result file in %s: %s" %
                    (check_result_path, e))


def close_checkresult_file():
    global checkresult_file_fd
    if checkresult_file_fd != None:
        os.close(checkresult_file_fd)
        file(checkresult_file_path + ".ok", "w")
        checkresult_file_fd = None


def core_pipe_open_timeout(signum, stackframe):
    raise IOError("Timeout while opening pipe")


def open_command_pipe():
    global nagios_command_pipe
    if nagios_command_pipe == None:
        if not os.path.exists(nagios_command_pipe_path):
            nagios_command_pipe = False # False means: tried but failed to open
            raise MKGeneralException("Missing core command pipe '%s'" % nagios_command_pipe_path)
        else:
            try:
                signal.signal(signal.SIGALRM, core_pipe_open_timeout)
                signal.alarm(3) # three seconds to open pipe
                nagios_command_pipe =  file(nagios_command_pipe_path, 'w')
                signal.alarm(0) # cancel alarm
            except Exception, e:
                nagios_command_pipe = False
                raise MKGeneralException("Error writing to command pipe: %s" % e)


def convert_perf_value(x):
    if x == None:
        return ""
    elif type(x) in [ str, unicode ]:
        return x
    elif type(x) == float:
        return ("%.6f" % x).rstrip("0").rstrip(".")
    else:
        return str(x)


def convert_perf_data(p):
    p = (map(convert_perf_value, p) + ['','','',''])[0:6]
    return "%s=%s;%s;%s;%s;%s" %  tuple(p)


def submit_check_result(host, servicedesc, result, sa, cached_at=None, cache_interval=None):
    if not result:
        result = 3, "Check plugin did not return any result"

    if len(result) != 3:
        raise MKGeneralException("Invalid check result: %s" % (result, ))
    state, infotext, perfdata = result

    if not (
        infotext.startswith("OK -") or
        infotext.startswith("WARN -") or
        infotext.startswith("CRIT -") or
        infotext.startswith("UNKNOWN -")):
        infotext = core_state_names[state] + " - " + infotext

    if isinstance(infotext, unicode):
        infotext = infotext.replace(u"|", u"\u2758")
    else:
        infotext = infotext.replace("|", u"\u2758".encode("utf8"))

    if sa != "":
        store_aggregated_service_result(host, servicedesc, sa, state, infotext)

    perftexts = []
    perftext = ""

    if perfdata:
        if len(perfdata) > 0 and type(perfdata[-1]) in (str, unicode):
            check_command = perfdata[-1]
            del perfdata[-1]
        else:
            check_command = None

        for p in perfdata:
            perftexts.append(convert_perf_data(p))

        if perftexts != []:
            if check_command and perfdata_format == "pnp":
                perftexts.append("[%s]" % check_command)
            perftext = "|" + (" ".join(perftexts))

    if not opt_dont_submit:
        submit_to_core(host, servicedesc, state, infotext + perftext, cached_at, cache_interval)

    if opt_verbose:
        if opt_showperfdata:
            infotext_fmt = "%-56s"
            p = ' (%s)' % (" ".join(perftexts))
        else:
            p = ''
            infotext_fmt = "%s"
        color = { 0: tty_green, 1: tty_yellow, 2: tty_red, 3: tty_magenta }[state]
        verbose(("%-20s %s%s"+infotext_fmt+"%s%s\n") % (servicedesc.encode('utf-8'),
                                       tty_bold, color, make_utf8(infotext.split('\n')[0]),
                                       tty_normal, make_utf8(p)))


def submit_to_core(host, service, state, output, cached_at = None, cache_interval = None):
    if opt_keepalive:
        add_keepalive_check_result(host, service, state, output, cached_at, cache_interval)

    elif check_submission == "pipe" or monitoring_core == "cmc":
        submit_via_command_pipe(host, service, state, output)

    elif check_submission == "file":
        submit_via_check_result_file(host, service, state, output)

    else:
        raise MKGeneralException("Invalid setting %r for check_submission. "
                                 "Must be 'pipe' or 'file'" % check_submission)


def submit_via_check_result_file(host, service, state, output):
    output = output.replace("\n", "\\n")
    open_checkresult_file()
    if checkresult_file_fd:
        now = time.time()
        os.write(checkresult_file_fd,
                """host_name=%s
service_description=%s
check_type=1
check_options=0
reschedule_check
latency=0.0
start_time=%.1f
finish_time=%.1f
return_code=%d
output=%s

""" % (host, make_utf8(service), now, now, state, make_utf8(output)))


def submit_via_command_pipe(host, service, state, output):
    output = output.replace("\n", "\\n")
    open_command_pipe()
    if nagios_command_pipe:
        nagios_command_pipe.write("[%d] PROCESS_SERVICE_CHECK_RESULT;%s;%s;%d;%s\n" %
                               (int(time.time()), host, make_utf8(service), state, make_utf8(output)))
        nagios_command_pipe.flush()



def make_utf8(x):
    if type(x) == unicode:
        return x.encode('utf-8')
    else:
        return x


def i_am_root():
    return os.getuid() == 0

def nodes_of(hostname):
    nodes = g_nodesof_cache.get(hostname, False)
    if nodes != False:
        return nodes

    for tagged_hostname, nodes in clusters.items():
        if hostname == tagged_hostname.split("|")[0]:
            g_nodesof_cache[hostname] = nodes
            return nodes

    g_nodesof_cache[hostname] = None
    return None

def check_uses_snmp(check_type):
    info_type = check_type.split(".")[0]
    return snmp_info.get(info_type) != None or \
       (info_type in inv_info and "snmp_info" in inv_info[info_type])

def regex(pattern):
    reg = g_compiled_regexes.get(pattern)
    if not reg:
        try:
            reg = re.compile(pattern)
        except Exception, e:
            raise MKGeneralException("Invalid regular expression '%s': %s" % (pattern, e))
        g_compiled_regexes[pattern] = reg
    return reg


def worst_monitoring_state(status_a, status_b):
    if status_a == 2 or status_b == 2:
        return 2
    else:
        return max(status_a, status_b)


def set_use_cachefile(state=True):
    global opt_use_cachefile, orig_opt_use_cachefile
    orig_opt_use_cachefile = opt_use_cachefile
    opt_use_cachefile = state


def ensure_directory(path):
    try:
        os.makedirs(path)
    except Exception, e:
        if os.path.exists(path):
            return
        raise

def utc_mktime(time_struct):
    import calendar
    return calendar.timegm(time_struct)


def check_levels(value, dsname, params, unit="", factor=1.0, scale=1.0, statemarkers=False):
    if unit:
        unit = " " + unit # Insert space before MB, GB, etc.
    perfdata = []
    infotexts = []

    def scale_value(v):
        if v == None:
            return None
        else:
            return v * factor * scale

    def levelsinfo_ty(ty, warn, crit, unit):
        return ("warn/crit %s %.2f/%.2f %s" % (ty, warn, crit, unit)).strip()

    if params == None or params == (None, None):
        return 0, "", []

    elif type(params) == tuple:
        if len(params) == 2: # upper warn and crit
            warn_upper, crit_upper = scale_value(params[0]), scale_value(params[1])
            warn_lower, crit_lower = None, None

        else: # upper and lower warn and crit
            warn_upper, crit_upper = scale_value(params[0]), scale_value(params[1])
            warn_lower, crit_lower = scale_value(params[2]), scale_value(params[3])

        ref_value = None

    else:
        try:
            ref_value, ((warn_upper, crit_upper), (warn_lower, crit_lower)) = \
                get_predictive_levels(dsname, params, "MAX", levels_factor=factor * scale)

            if ref_value:
                infotexts.append("predicted reference: %.2f%s" % (ref_value / scale, unit))
            else:
                infotexts.append("no reference for prediction yet")

        except MKGeneralException, e:
            ref_value = None
            warn_upper, crit_upper, warn_lower, crit_lower = None, None, None, None
            infotexts.append("no reference for prediction (%s)" % e)

        except Exception, e:
            if opt_debug:
                raise
            return 3, "%s" % e, []

    if ref_value:
        perfdata.append(('predict_' + dsname, ref_value))

    if crit_upper != None and value >= crit_upper:
        state = 2
        infotexts.append(levelsinfo_ty("at", warn_upper / scale, crit_upper / scale, unit))
    elif crit_lower != None and value < crit_lower:
        state = 2
        infotexts.append(levelsinfo_ty("below", warn_lower / scale, crit_lower / scale, unit))

    elif warn_upper != None and value >= warn_upper:
        state = 1
        infotexts.append(levelsinfo_ty("at", warn_upper / scale, crit_upper / scale, unit))
    elif warn_lower != None and value < warn_lower:
        state = 1
        infotexts.append(levelsinfo_ty("below", warn_lower / scale, crit_lower / scale, unit))

    else:
        state = 0

    if infotexts:
        infotext = " (" + ", ".join(infotexts) + ")"
    else:
        infotext = ""

    if state and statemarkers:
        if state == 1:
            infotext += "(!)"
        else:
            infotext += "(!!)"
    return state, infotext, perfdata


def within_range(value, minv, maxv):
    if value >= 0:
        return value >= minv and value <= maxv
    else:
        return value <= minv and value >= maxv

def saveint(i):
    try:
        return int(i)
    except:
        return 0

def tryint(x):
    try:
        return int(x)
    except:
        return x


def savefloat(f):
    try:
        return float(f)
    except:
        return 0.0

def binstring_to_int(binstring):
    value = 0
    mult = 1
    for byte in binstring[::-1]:
        value += mult * ord(byte)
        mult *= 256
    return value


def get_bytes_human_readable(b, base=1024.0, bytefrac=True, unit="B"):
    base = float(base)
    prefix = ''
    if b < 0:
        prefix = '-'
        b *= -1

    if b >= base * base * base * base:
        return '%s%.2f T%s' % (prefix, b / base / base / base / base, unit)
    elif b >= base * base * base:
        return '%s%.2f G%s' % (prefix, b / base / base / base, unit)
    elif b >= base * base:
        return '%s%.2f M%s' % (prefix, b / base / base, unit)
    elif b >= base:
        return '%s%.2f k%s' % (prefix, b / base, unit)
    elif bytefrac:
        return '%s%.2f %s' % (prefix, b, unit)
    else: # Omit byte fractions
        return '%s%.0f %s' % (prefix, b, unit)

def get_filesize_human_readable(size):
    if size < 4 * 1024 * 1024:
        return "%d B" % int(size)
    elif size < 4 * 1024 * 1024 * 1024:
        return "%.2f MB" % (float(size) / (1024 * 1024))
    else:
        return "%.2f GB" % (float(size) / (1024 * 1024 * 1024))


def get_nic_speed_human_readable(speed):
    try:
        speedi = int(speed)
        if speedi == 10000000:
            speed = "10 Mbit/s"
        elif speedi == 100000000:
            speed = "100 Mbit/s"
        elif speedi == 1000000000:
            speed = "1 Gbit/s"
        elif speedi < 1500:
            speed = "%d bit/s" % speedi
        elif speedi < 1000000:
            speed = "%.1f Kbit/s" % (speedi / 1000.0)
        elif speedi < 1000000000:
            speed = "%.2f Mbit/s" % (speedi / 1000000.0)
        else:
            speed = "%.2f Gbit/s" % (speedi / 1000000000.0)
    except:
        pass
    return speed


def get_timestamp_human_readable(timestamp):
    if timestamp:
        return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(float(timestamp)))
    else:
        return "never"


def get_age_human_readable(secs):
    if secs < 240:
        return "%d sec" % secs
    mins = secs / 60
    if mins < 120:
        return "%d min" % mins
    hours, mins = divmod(mins, 60)
    if hours < 12 and mins > 0:
        return "%d hours %d min" % (hours, mins)
    elif hours < 48:
        return "%d hours" % hours
    days, hours = divmod(hours, 24)
    if days < 7 and hours > 0:
        return "%d days %d hours" % (days, hours)
    return "%d days" % days


def get_relative_date_human_readable(timestamp):
    now = time.time()
    if timestamp > now:
        return "in " + get_age_human_readable(timestamp - now)
    else:
        return get_age_human_readable(now - timestamp) + " ago"

def get_percent_human_readable(perc, precision=2):
    if perc > 0:
        perc_precision = max(1, 2 - int(round(math.log(perc, 10))))
    else:
        perc_precision = 1
    return "%%.%df%%%%" % perc_precision % perc


def quote_shell_string(s):
    return "'" + s.replace("'", "'\"'\"'") + "'"

def camelcase_to_underscored(name):
    previous_lower = False
    previous_underscore = True
    result = ""
    for c in name:
        if c.isupper():
            if previous_lower and not previous_underscore:
                result += "_"
            previous_lower = False
            previous_underscore = False
            result += c.lower()
        elif c == "_":
            previous_lower = False
            previous_underscore = True
            result += c
        else:
            previous_lower = True
            previous_underscore = False
            result += c
    return result


def simple_livestatus_query(lql):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.connect(livestatus_unix_socket)
    s.send(lql)
    s.shutdown(socket.SHUT_WR)
    response = ""
    while True:
        chunk = s.recv(4096)
        if not chunk:
            break
        response += chunk
    return response


def check_timeperiod(timeperiod):
    global g_inactive_timerperiods
    if g_inactive_timerperiods == None:
        try:
            response = simple_livestatus_query("GET timeperiods\nColumns: name\nFilter: in = 0\n")
            g_inactive_timerperiods = response.splitlines()
        except MKTimeout:
            raise

        except Exception, e:
            if opt_debug:
                raise
            else:
                return True

    return timeperiod not in g_inactive_timerperiods


def get_effective_service_level():
    service_levels = service_extra_conf(g_hostname, g_service_description,
                                        service_service_levels)

    if service_levels:
        return service_levels[0]
    else:
        service_levels = host_extra_conf(g_hostname, host_service_levels)
        if service_levels:
            return service_levels[0]
    return 0



def summary_hostname(hostname):
    return aggr_summary_hostname % hostname

def store_aggregated_service_result(hostname, detaildesc, aggrdesc, newstatus, newoutput):
    global g_aggregated_service_results
    count, status, outputlist = g_aggregated_service_results.get(aggrdesc, (0, 0, []))
    if status_worse(newstatus, status):
        status = newstatus
    if newstatus > 0 or aggregation_output_format == "multiline":
        outputlist.append( (newstatus, detaildesc, newoutput) )
    g_aggregated_service_results[aggrdesc] = (count + 1, status, outputlist)

def status_worse(newstatus, status):
    if status == 2:
        return False # nothing worse then critical
    elif newstatus == 2:
        return True  # nothing worse then critical
    else:
        return newstatus > status # 0 < 1 < 3 are in correct order

def submit_aggregated_results(hostname):
    if not host_is_aggregated(hostname):
        return

    if opt_verbose:
        print "\n%s%sAggregates Services:%s" % (tty_bold, tty_blue, tty_normal)
    global g_aggregated_service_results
    items = g_aggregated_service_results.items()
    items.sort()
    aggr_hostname = summary_hostname(hostname)
    for servicedesc, (count, status, outputlist) in items:
        if aggregation_output_format == "multiline":
            longoutput = ""
            statuscounts = [ 0, 0, 0, 0 ]
            for itemstatus, item, output in outputlist:
                longoutput += '\\n%s: %s' % (item, output)
                statuscounts[itemstatus] = statuscounts[itemstatus] + 1
            summarytexts = [ "%d service%s %s" % (x[0], x[0] != 1 and "s" or "", x[1])
                           for x in zip(statuscounts, ["OK", "WARN", "CRIT", "UNKNOWN" ]) if x[0] > 0 ]
            text = ", ".join(summarytexts) + longoutput
        else:
            if status == 0:
                text = "OK - %d services OK" % count
            else:
                text = " *** ".join([ item + " " + output for itemstatus, item, output in outputlist ])

        if not opt_dont_submit:
            submit_to_core(aggr_hostname, servicedesc, status, text)

        if opt_verbose:
            color = { 0: tty_green, 1: tty_yellow, 2: tty_red, 3: tty_magenta }[status]
            lines = text.split('\\n')
            print "%-20s %s%s%-70s%s" % (servicedesc, tty_bold, color, lines[0], tty_normal)
            if len(lines) > 1:
                for line in lines[1:]:
                    print "  %s" % line
                print "-------------------------------------------------------------------------------"


def submit_check_mk_aggregation(hostname, status, output):
    if not host_is_aggregated(hostname):
        return

    if not opt_dont_submit:
        submit_to_core(summary_hostname(hostname), "Check_MK", status, output)

    if opt_verbose:
        color = { 0: tty_green, 1: tty_yellow, 2: tty_red, 3: tty_magenta }[status]
        print "%-20s %s%s%-70s%s" % ("Check_MK", tty_bold, color, output, tty_normal)



def interrupt_handler(signum, frame):
    sys.stderr.write('<Interrupted>\n')
    sys.exit(1)


def register_sigint_handler():
    signal.signal(signal.SIGINT, interrupt_handler)



def handle_keepalive_interrupt(signum, frame):
    raise MKTerminate()


def register_keepalive_sigint_handler():
    signal.signal(signal.SIGINT, handle_keepalive_interrupt)
register_sigint_handler()




def get_rrd_data(hostname, service_description, varname, cf, fromtime, untiltime):
    step = 1
    rpn = "%s.%s" % (varname, cf.lower()) # "MAX" -> "max"
    lql = "GET services\n" \
          "Columns: rrddata:m1:%s:%d:%d:%d\n" \
          "OutputFormat: python\n" \
          "Filter: host_name = %s\n" \
          "Filter: description = %s\n" % (
             rpn, fromtime, untiltime, step, hostname, service_description)
    try:
        response = eval(simple_livestatus_query(lql))[0][0]
    except Exception, e:
        if opt_debug:
            raise
        raise MKGeneralException("Cannot get historic metrics via Livestatus: %s" % e)

    if not response:
        raise MKGeneralException("Got no historic metrics")

    real_fromtime, real_untiltime, step = response[:3]
    values = response[3:]
    return step, values


daynames = [ "monday", "tuesday", "wednesday", "thursday",
             "friday", "saturday", "sunday"]

def is_dst(timestamp):
    return time.localtime(timestamp).tm_isdst

def timezone_at(timestamp):
    if is_dst(timestamp):
        return time.altzone
    else:
        return time.timezone

def group_by_wday(t):
    wday = time.localtime(t).tm_wday
    day_of_epoch, rel_time = divmod(t - timezone_at(t), 86400)
    return daynames[wday], rel_time

def group_by_day(t):
    return "everyday", (t - timezone_at(t)) % 86400

def group_by_day_of_month(t):
    broken = time.localtime(t)
    mday = broken[2]
    return str(mday), (t - timezone_at(t)) % 86400

def group_by_everyhour(t):
    return "everyhour", (t - timezone_at(t)) % 3600


prediction_periods = {
    "wday" : {
        "slice"     : 86400, # 7 slices
        "groupby"   : group_by_wday,
        "valid"     : 7,
    },
    "day" : {
        "slice"     : 86400, # 31 slices
        "groupby"   : group_by_day_of_month,
        "valid"     : 28,
    },
    "hour" : {
        "slice"     : 86400, # 1 slice
        "groupby"   : group_by_day,
        "valid"     : 1,
    },
    "minute" : {
        "slice"     : 3600, # 1 slice
        "groupby"   : group_by_everyhour,
        "valid"     : 24,
    },
}


def get_prediction_timegroup(t, period_info):
    timegroup, rel_time = period_info["groupby"](t)
    from_time = t - rel_time
    until_time = t - rel_time + period_info["slice"]
    return timegroup, from_time, until_time, rel_time


def compute_prediction(pred_file, timegroup, params, period_info, from_time, dsname, cf):
    begin = from_time
    slices = []
    absolute_begin = from_time - params["horizon"] * 86400


    smallest_step = None
    while begin >= absolute_begin:
        tg, fr, un, rel = get_prediction_timegroup(begin, period_info)
        if tg == timegroup:
            step, data = get_rrd_data(g_hostname, g_service_description,
                                      dsname, cf, fr, un-1)
            if smallest_step == None:
                smallest_step = step
            slices.append((fr, step / smallest_step, data))
        begin -= period_info["slice"]

    num_points = len(slices[0][2])
    consolidated = []
    for i in xrange(num_points):
        point_line = []
        for from_time, scale, data in slices:
            idx = int(i / float(scale))
            if idx < len(data):
                d = data[idx]
                if d != None:
                    point_line.append(d)

        if point_line:
            average = sum(point_line) / len(point_line)
            consolidated.append([
                 average,
                 min(point_line),
                 max(point_line),
                 stdev(point_line, average),
            ])
        else:
            consolidated.append([None, None, None, None])

    result = {
        "num_points" : num_points,
        "step"       : smallest_step,
        "columns"    : [ "average", "min", "max", "stdev" ],
        "points"     : consolidated,
    }
    return result

def stdev(point_line, average):
    return math.sqrt(sum([ (p-average)**2 for p in point_line ]) / len(point_line))


def get_predictive_levels(dsname, params, cf, levels_factor=1.0):
    now = time.time()
    period_info = prediction_periods[params["period"]]

    timegroup, from_time, until_time, rel_time = \
       get_prediction_timegroup(now, period_info)

    dir = "%s/prediction/%s/%s/%s" % (var_dir, g_hostname,
             pnp_cleanup(g_service_description), pnp_cleanup(dsname))
    if not os.path.exists(dir):
        os.makedirs(dir)

    pred_file = "%s/%s" % (dir, timegroup)
    info_file = pred_file + ".info"

    for file_path in [ pred_file, info_file ]:
        if os.path.exists(file_path) and os.stat(file_path).st_size == 0:
            os.unlink(file_path)

    try:
        last_info = eval(file(info_file).read())
        for k, v in params.items():
            if last_info.get(k) != v:
                if opt_debug:
                    sys.stderr.write("Prediction parameters have changed.\n")
                last_info = None
                break
    except IOError:
        if opt_debug:
            sys.stderr.write("No previous prediction for group %s available.\n" % timegroup)
        last_info = None

    if last_info and last_info["time"] + period_info["valid"] * period_info["slice"] < now:
        if opt_debug:
            sys.stderr.write("Prediction of %s outdated.\n" % timegroup)
        last_info = None

    if last_info:
        prediction = eval(file(pred_file).read())

    else:
        for f in os.listdir(dir):
            if f.endswith(".info"):
                try:
                    info = eval(file(dir + "/" + f).read())
                    if info["period"] != params["period"]:
                        if opt_debug:
                            sys.stderr.write("Removing obsolete prediction %s\n" % f[:-5])
                        os.remove(dir + "/" + f)
                        os.remove(dir + "/" + f[:-5])
                except:
                    pass

        if opt_debug:
            sys.stderr.write("Computing prediction for time group %s.\n" % timegroup)
        prediction = compute_prediction(pred_file, timegroup, params, period_info, from_time, dsname, cf)
        info = {
            "time"         : now,
            "range"        : (from_time, until_time),
            "cf"           : cf,
            "dsname"       : dsname,
            "slice"        : period_info["slice"],
        }
        info.update(params)
        file(info_file, "w").write("%r\n" % info)
        file(pred_file, "w").write("%r\n" % prediction)

    index = int(rel_time / prediction["step"])
    reference = dict(zip(prediction["columns"], prediction["points"][index]))
    ref_value = reference["average"]
    stdev = reference["stdev"]
    levels = []
    if not ref_value: # No reference data available
        levels = ((None, None), (None, None))
    else:
        for what, sig in [ ( "upper", 1 ), ( "lower", -1 )]:
            p = "levels_" + what
            if p in params:
                how, (warn, crit) = params[p]
                if how == "absolute":
                    this_levels = (ref_value + (sig * warn * levels_factor), ref_value + (sig * crit * levels_factor))
                elif how == "relative":
                    this_levels = (ref_value + sig * (ref_value * warn / 100),
                                   ref_value + sig * (ref_value * crit / 100))
                else: #  how == "stdev":
                    this_levels = (ref_value + sig * (stdev * warn),
                                  ref_value + sig * (stdev * crit))

                if what == "upper" and "levels_upper_min" in params:
                    limit_warn, limit_crit = params["levels_upper_min"]
                    this_levels = (max(limit_warn, this_levels[0]), max(limit_crit, this_levels[1]))
                levels.append(this_levels)
            else:
                levels.append((None, None))


    return ref_value, levels


def pnp_cleanup(s):
    return s \
        .replace(' ',  '_') \
        .replace(':',  '_') \
        .replace('/',  '_') \
        .replace('\\', '_')

# very simple commandline parsing: only -v and -d are supported
opt_verbose = ('-v' in sys.argv) and 1 or 0
opt_debug   = '-d' in sys.argv

# make sure these names are defined (even if never needed)
no_discovery_possible = None

# Global variables
check_mk_version = '1.2.8p15'
tcp_connect_timeout = 5.0
agent_min_version = 0
perfdata_format = 'pnp'
aggregation_output_format = 'multiline'
aggr_summary_hostname = '%s-s'
nagios_command_pipe_path = '/omd/sites/prod/tmp/run/nagios.cmd'
check_result_path = '/omd/sites/prod/tmp/nagios/checkresults'
check_submission = 'file'
monitoring_core = 'nagios'
var_dir = '/omd/sites/prod/var/check_mk'
counters_directory = '/omd/sites/prod/tmp/check_mk/counters'
tcp_cache_dir = '/omd/sites/prod/tmp/check_mk/cache'
tmp_dir = '/omd/sites/prod/tmp/check_mk'
log_dir = '/omd/sites/prod/var/log'
snmpwalks_dir = '/omd/sites/prod/var/check_mk/snmpwalks'
check_mk_basedir = '/omd/sites/prod/etc/check_mk'
nagios_user = 'prod'
omd_root = '/omd/sites/prod'
www_group = 'prod'
cluster_max_cachefile_age = 90
check_max_cachefile_age = 0
piggyback_max_cachefile_age = 3600
fallback_agent_output_encoding = 'latin1'
simulation_mode = False
agent_simulator = False
aggregate_check_mk = False
check_mk_perfdata_with_times = True
livestatus_unix_socket = '/omd/sites/prod/tmp/run/live'
use_inline_snmp = True
record_inline_snmp_stats = False

# Checks for mgen1.gate.rtf

def get_precompiled_check_table(hostname, remove_duplicates=False, world='config'):
    return [('cpu.loads', None, (5.0, 10.0), u'CPU load', ''), ('kernel.util', None, {}, u'CPU utilization', ''), ('diskstat', u'SUMMARY', {}, u'Disk IO SUMMARY', ''), ('df', u'/', {'trend_range': 24, 'show_levels': 'onmagic', 'inodes_levels': (10.0, 5.0), 'magic_normsize': 20, 'show_inodes': 'onlow', 'levels': (80.0, 90.0), 'show_reserved': False, 'levels_low': (50.0, 60.0), 'trend_perfdata': True}, u'Filesystem /', ''), ('df', u'/data', {'trend_range': 24, 'show_levels': 'onmagic', 'inodes_levels': (10.0, 5.0), 'magic_normsize': 20, 'show_inodes': 'onlow', 'levels': (80.0, 90.0), 'show_reserved': False, 'levels_low': (50.0, 60.0), 'trend_perfdata': True}, u'Filesystem /data', ''), ('df', u'/home', {'trend_range': 24, 'show_levels': 'onmagic', 'inodes_levels': (10.0, 5.0), 'magic_normsize': 20, 'show_inodes': 'onlow', 'levels': (80.0, 90.0), 'show_reserved': False, 'levels_low': (50.0, 60.0), 'trend_perfdata': True}, u'Filesystem /home', ''), ('local', u'HD_/tmp/fmq/SpolMonCtrl', None, u'HD_/tmp/fmq/SpolMonCtrl', ''), ('local', u'HD_/tmp/fmq/moments/sband/shmem_20000', None, u'HD_/tmp/fmq/moments/sband/shmem_20000', ''), ('local', u'HD_/tmp/fmq/syscon', None, u'HD_/tmp/fmq/syscon', ''), ('local', u'HD_/tmp/fmq/ts/sband/shmem_10000', None, u'HD_/tmp/fmq/ts/sband/shmem_10000', ''), ('local', u'HP_DataMapper_primary', None, u'HP_DataMapper_primary', ''), ('local', u'HP_DsFileDist_suncal', None, u'HP_DsFileDist_suncal', ''), ('local', u'HP_DsFileDist_time_series', None, u'HP_DsFileDist_time_series', ''), ('local', u'HP_DsServerMgr_primary', None, u'HP_DsServerMgr_primary', ''), ('local', u'HP_Fmq2Fmq_moments.sband', None, u'HP_Fmq2Fmq_moments.sband', ''), ('local', u'HP_Fmq2Fmq_moments.sband2', None, u'HP_Fmq2Fmq_moments.sband2', ''), ('local', u'HP_Fmq2Fmq_ts.sband', None, u'HP_Fmq2Fmq_ts.sband', ''), ('local', u'HP_Fmq2Fmq_ts.sband2', None, u'HP_Fmq2Fmq_ts.sband2', ''), ('local', u'HP_Iq2Dsr_sband', None, u'HP_Iq2Dsr_sband', ''), ('local', u'HP_Janitor_logs', None, u'HP_Janitor_logs', ''), ('local', u'HP_Janitor_time_series', None, u'HP_Janitor_time_series', ''), ('local', u'HP_RadMon_log.sband', None, u'HP_RadMon_log.sband', ''), ('local', u'HP_Scout_primary', None, u'HP_Scout_primary', ''), ('local', u'HP_SpolAngles2Fmq_s2d', None, u'HP_SpolAngles2Fmq_s2d', ''), ('local', u'HP_SpolSysconRelay_sband', None, u'HP_SpolSysconRelay_sband', ''), ('local', u'HP_SpolTs2Fmq_sband', None, u'HP_SpolTs2Fmq_sband', ''), ('local', u'HP_SpolTsMonitor_sband', None, u'HP_SpolTsMonitor_sband', ''), ('local', u'HP_SunCal_sband', None, u'HP_SunCal_sband', ''), ('local', u'HP_TsTcp2Fmq_rvp8', None, u'HP_TsTcp2Fmq_rvp8', ''), ('local', u'HawkSummary_Data', None, u'HawkSummary_Data', ''), ('local', u'HawkSummary_Processes', None, u'HawkSummary_Processes', ''), ('ipmi_sensors', u'Fan_Fan1', None, u'IPMI Sensor Fan_Fan1', ''), ('ipmi_sensors', u'Fan_Fan2', None, u'IPMI Sensor Fan_Fan2', ''), ('ipmi_sensors', u'Fan_Fan3', None, u'IPMI Sensor Fan_Fan3', ''), ('ipmi_sensors', u'Fan_Fan4', None, u'IPMI Sensor Fan_Fan4', ''), ('ipmi_sensors', u'Fan_Fan5', None, u'IPMI Sensor Fan_Fan5', ''), ('ipmi_sensors', u'Fan_Fan6', None, u'IPMI Sensor Fan_Fan6', ''), ('ipmi_sensors', u'Fan_Fan_Redundancy', None, u'IPMI Sensor Fan_Fan_Redundancy', ''), ('ipmi_sensors', u'Temperature_Exhaust_Temp', None, u'IPMI Sensor Temperature_Exhaust_Temp', ''), ('ipmi_sensors', u'Temperature_Inlet_Temp', None, u'IPMI Sensor Temperature_Inlet_Temp', ''), ('ipmi_sensors', u'Temperature_Temp', None, u'IPMI Sensor Temperature_Temp', ''), ('lnx_if', u'2', {'state': ['1'], 'errors': (0.01, 0.1), 'speed': 1000000000}, u'Interface 2', ''), ('kernel', u'Context Switches', None, u'Kernel Context Switches', ''), ('kernel', u'Major Page Faults', None, u'Kernel Major Page Faults', ''), ('kernel', u'Process Creations', None, u'Kernel Process Creations', ''), ('logins', None, (20, 30), u'Logins', ''), ('mem.linux', None, {'levels_total': ('perc_used', (120.0, 150.0)), 'levels_shm': ('perc_used', (20.0, 30.0)), 'levels_commitlimit': ('perc_free', (20.0, 10.0)), 'levels_virtual': ('perc_used', (80.0, 90.0)), 'levels_vmalloc': ('abs_free', (52428800, 31457280)), 'levels_committed': ('perc_used', (100.0, 150.0)), 'levels_pagetables': ('perc_used', (8.0, 16.0))}, u'Memory', ''), ('mounts', u'/', [u'data=ordered', u'relatime', u'rw'], u'Mount options of /', ''), ('mounts', u'/data', [u'data=ordered', u'relatime', u'rw'], u'Mount options of /data', ''), ('mounts', u'/home', [u'data=ordered', u'relatime', u'rw'], u'Mount options of /home', ''), ('chrony', None, {'ntp_levels': (10, 200.0, 500.0), 'alert_delay': (300, 3600)}, u'NTP Time', ''), ('cpu.threads', None, (2000, 4000), u'Number of threads', ''), ('postfix_mailq', None, {'active': (200, 300), 'deferred': (10, 20)}, u'Postfix Queue', ''), ('local', u'SBandAntennaMovement_stationaryPeriod', None, u'SBandAntennaMovement_stationaryPeriod', ''), ('tcp_conn_stats', None, {}, u'TCP Connections', ''), ('uptime', None, {}, u'Uptime', '')]

precompiled_check_intervals = {}
def check_interval_of(hostname, checktype):
    return precompiled_check_intervals.get(checktype)

precompiled_service_timeperiods = {}
def check_period_of(hostname, service):
    return precompiled_service_timeperiods.get(service)

has_inline_snmp = False
check_info = {}
inv_info = {}
check_includes = {}
precompile_params = {}
factory_settings = {}
checkgroup_of = {}
check_config_variables = []
check_default_levels = {}
snmp_info = {}
snmp_scan_functions = {}
# /omd/sites/prod/share/check_mk/checks/cpu_util.include




def cpu_util_core_name(orig, core_counter):
    expr = regex("\d+$")
    match = expr.search(orig)
    if match is not None:
        num = match.group(0)
    else:
        num = core_counter
        core_counter += 1
    return "cpu_core_util_%s" % num, core_counter


def check_cpu_util(util, params, this_time = None, cores = None):
    if this_time == None:
        this_time = time.time()

    if params == None:
        params = {}
    elif type(params) == tuple:
        params = {
            "levels" : params,
        }

    infotext = "%.1f%% used" % util

    if "average" in params:
        util_avg = get_average("cpu_utilization.avg", this_time, util, params["average"])
        check_against = util_avg
        perfvar = "avg"
        infotext += ", %dmin average: %.1f%%" % (params["average"], util_avg)
    else:
        check_against = util
        perfvar = "util"


    levels = params.get("levels")
    if type(levels) == tuple:
        warn, crit = levels # only for perfdata
    else:
        warn, crit = None, None

    state, extrainfo, extraperf = check_levels(check_against, perfvar, levels)
    if extrainfo:
        infotext += "," + extrainfo

    perfdata = [ ("util", util, warn, crit, 0, 100) ]
    if "average" in params:
        perfdata.append( ("avg", util_avg, warn, crit, 0, 100) )

    perfdata += extraperf # reference curve for predictive levels
    yield state, infotext, perfdata

    if cores and ("core_util_graph" in params or "core_util_time" in params):
        core_counter = 0
        for core, total_perc in cores:
            if "core_util_graph" in params:
                core_name, core_counter = cpu_util_core_name(core, core_counter)
                yield 0, None, [(core_name, total_perc)]

            if "core_util_time" in params:
                threshold, warn_core, crit_core = params["core_util_time"]
                core_state_name = "cpu.util.core.high.%s" % core
                if total_perc > threshold:
                    timestamp = get_item_state(core_state_name, 0)
                    high_load_duration = (this_time - timestamp)
                    if timestamp == 0:
                        set_item_state(core_state_name, this_time)
                    elif high_load_duration > crit_core:
                        yield 2, "%s is under high load for %s minutes (warn/crit at %s/%s minutes)" %\
                            (core, high_load_duration / 60, warn_core / 60, crit_core / 60), None
                    elif high_load_duration > warn_core:
                        yield 1, "%s is under high load for %s minutes (warn/crit at %s/%s minutes)" %\
                            (core, high_load_duration / 60, warn_core / 60, crit_core / 60), None
                else:
                    clear_item_state(core_state_name)


def check_cpu_util_unix(values, params, cores = None):
    this_time = int(time.time())
    diff_values = []
    n = 0
    for v in values:
        n += 1
        countername = "cpu.util.%d" % n
        last_time, last_val = get_item_state(countername, (0, 0))
        diff_values.append(v - last_val)
        set_item_state(countername, (this_time, v))

    sum_jiffies = sum(diff_values) # do not account for steal!
    if sum_jiffies == 0:
        raise MKCounterWrapped("Too short time difference since last check")

    user        = diff_values[0] + diff_values[1] # add user + nice
    system      = diff_values[2] + diff_values[5] + diff_values[6]
    wait        = diff_values[4]
    user_perc   = 100.0 * float(user)   / float(sum_jiffies)
    system_perc = 100.0 * float(system) / float(sum_jiffies)
    wait_perc   = 100.0 * float(wait)   / float(sum_jiffies)
    perfdata = [
          ( "user",   "%.3f" % user_perc ),
          ( "system", "%.3f" % system_perc ),
          ( "wait",   "%.3f" % wait_perc ) ]

    yield 0, "user: %.1f%%, system: %.1f%%" % (user_perc, system_perc), perfdata

    state = 0
    if "iowait" in params and params["iowait"] != None:
        warn, crit = params["iowait"]
        if wait_perc >= crit:
            state = 2
        elif wait_perc >= warn:
            state = 1
    yield state, "wait: %.1f%%" % (wait_perc)

    if len(values) >= 8: #  and values[7]:
        steal = diff_values[7]
        steal_perc = 100.0 * float(steal) / float(sum_jiffies)
        yield 0, "steal: %.1f%%" % steal_perc, [ ("steal", steal_perc) ]
    else:
        steal_perc = 0

    if len(values) >= 10: # and (values[8] or values[9]):
        guest = diff_values[8] + diff_values[9]
        guest_perc = 100.0 * float(guest) / float(sum_jiffies)
        yield 0, "guest: %.1f%%" % guest_perc, [ ("guest", guest_perc) ]
    else:
        guest_perc = 0

    util_total_perc = user_perc + system_perc + wait_perc + steal_perc + guest_perc
    state = 0
    levelstext = ""
    if "util" in params:
        warn, crit = params["util"]
        if util_total_perc >= crit:
            state = 2
        elif util_total_perc >= warn:
            state = 1
        else:
            state = 0
        if state:
            levelstext = " (warn/crit at %.1f%%/%.1f%%)" % (warn, crit)

    yield state, "total: %.1f%%" % util_total_perc + levelstext

    if cores and\
            ("core_util_graph" in params or \
             "core_util_time" in params):
        core_counter = 0
        cores_padded = [line + [0] * (11 - len(line)) for line in cores]
        for core, user, nice, system, idle, iowait,\
            irq, softirq, steal, guest, guest_nice in cores_padded:

            total = user + nice + system + iowait + irq + softirq + steal + guest + guest_nice

            prev_total = get_item_state("cpu.util.%s.total" % core, 0)
            total_diff = total - prev_total
            set_item_state("cpu.util.%s.total" % core, total)

            total_perc = ((100.0 * total_diff) / sum_jiffies) * len(cores)

            if "core_util_graph" in params:
                core_name, core_counter = cpu_util_core_name(core, core_counter)
                yield 0, None, [(core_name, total_perc)]

            if "core_util_time" in params:
                threshold, warn_core, crit_core = params["core_util_time"]
                core_state_name = "cpu.util.core.high.%s" % core
                if total_perc > threshold:
                    timestamp = get_item_state(core_state_name, 0)
                    high_load_duration = (this_time - timestamp)
                    if timestamp == 0:
                        set_item_state(core_state_name, this_time)
                    elif high_load_duration > crit_core:
                        yield 2, "%s is under high load for %s minutes (warn/crit at %s/%s minutes)" %\
                            (core, high_load_duration / 60, warn_core / 60, crit_core / 60)
                    elif high_load_duration > warn_core:
                        yield 1, "%s is under high load for %s minutes (warn/crit at %s/%s minutes)" %\
                            (core, high_load_duration / 60, warn_core / 60, crit_core / 60)
                else:
                    clear_item_state(core_state_name)



# /omd/sites/prod/share/check_mk/checks/kernel


inventory_kernel_counters = [ "pgmajfault", "ctxt", "processes" ]
kernel_default_levels = None

kernel_counter_names = {
  "ctxt"       : "Context Switches",
  "processes"  : "Process Creations",
  "pgmajfault" : "Major Page Faults",
}

def inventory_kernel(info):
    inventory = []
    for counter in inventory_kernel_counters:
        hits = [ line[0] for line in info[1:] if line[0] == counter ]
        if len(hits) == 1:
            countername = kernel_counter_names.get(counter, counter)
            inventory.append( (countername, "kernel_default_levels") )
    return inventory


def check_kernel(item, params, info):
    if not info:
        return

    this_time = int(info[0][0])
    hits = [ (line[0], line[1])
             for line in info[1:]
             if line[0] == item or kernel_counter_names.get(line[0], line[0]) == item ]
    if len(hits) == 0:
        return (3, "item '%s' not found in agent output" % item)
    elif len(hits) > 1:
        return (3, "item '%s' not unique (found %d times)" % (item, len(hits)))

    counter = hits[0][0]
    this_val = int(hits[0][1])
    per_sec = get_rate(None, this_time, this_val)

    if type(params) == tuple:
        warn, crit = params
    else:
        warn, crit = None, None
    perfdata = [ (counter, per_sec, warn, crit) ]
    state, text, extraperf = check_levels(per_sec, counter, params)
    perfdata += extraperf
    infotext = "%.0f/s" % per_sec
    if text:
        infotext += ", " + text
    return state, infotext, perfdata


check_info["kernel"] = {
    'check_function':          check_kernel,
    'inventory_function':      inventory_kernel,
    'service_description':     'Kernel %s',
    'has_perfdata':            True,
    'group':                   'vm_counter',
}


kernel_util_default_levels = None

def inventory_cpu_utilization(info):
    for x in info:
        if len(x) > 0 and x[0] == 'cpu':
            return [(None, {})]


def transform_cpu_info(element):
    if len(element) < 8:
        element += ['0', '0', '0', '0'] # needed for Linux 2.4

    return [element[0]] + [int(x) for x in element[1:]]


def kernel_check_cpu_utilization(item, params, info):
    if type(params) != dict:
        params = { "iowait": params }

    total = [transform_cpu_info(line)
         for line in info
         if line[0] == "cpu"]

    if len(total) != 1:
        return 3, "More than one line with CPU info found. This check is not cluster-enabled."

    cores = [transform_cpu_info(line)
             for line in info
             if line[0].startswith("cpu") and len(line[0]) > 3]
    return check_cpu_util_unix(total[0][1:], params, cores)

check_info["kernel.util"] = {
    'check_function':           kernel_check_cpu_utilization,
    'inventory_function':       inventory_cpu_utilization,
    'service_description':      'CPU utilization',
    'has_perfdata':             True,
    'default_levels_variable':  'kernel_util_default_levels',
    'group':                    'cpu_iowait',
    'includes':                 ['cpu_util.include'],
}



# /omd/sites/prod/share/check_mk/checks/uptime.include



def parse_snmp_uptime(ticks):
    try:
        if len(ticks) < 3:
            return 0
        else:
            return int(ticks[:-2])
    except:
        days, h, m, s = ticks.split(":")
        return (int(days) * 86400 ) + (int(h) * 3600) + (int(m) * 60) + int(float(s))


def check_uptime_seconds(params, uptime_sec):
    seconds  = uptime_sec % 60
    rem      = uptime_sec / 60
    minutes  = rem % 60
    hours    = (rem % 1440) / 60
    days     = rem / 1440
    since    = time.strftime("%c", time.localtime(time.time() - uptime_sec))

    state    = 0
    infotext = "up since %s (%dd %02d:%02d:%02d)" % \
                (since, days, hours, minutes, seconds)

    if params == None: # legacy: support older versions of parameters
        params = {}

    if "min" in params:
        warn, crit = params["min"]
        if uptime_sec < crit:
            state = 2
        elif uptime_sec < warn:
            state = max(state, 1)

        if state:
            infotext += ", not up long enough!"

    if "max" in params:
        warn, crit = params["max"]
        if uptime_sec > crit:
            state = 2
        elif uptime_sec > warn:
            state = max(state, 1)

        if uptime_sec > warn:
            infotext += ", up too long!"

    return (state,  infotext, [ ("uptime", uptime_sec) ])



# /omd/sites/prod/share/check_mk/checks/uptime



def inventory_uptime(info):
    if info:
        return [ (None, {}) ]

def check_uptime(_no_item, params, info):
    uptime_sec = float(info[0][0])
    return check_uptime_seconds(params, uptime_sec)


check_info["uptime"] = {
    'check_function'      : check_uptime,
    'inventory_function'  : inventory_uptime,
    'service_description' : 'Uptime',
    'has_perfdata'        : True,
    'includes'            : [ 'uptime.include' ],
    'group'               : 'uptime',
}


# /omd/sites/prod/share/check_mk/checks/chrony

ntp_default_levels = (10, 200.0, 500.0) # stratum, ms offset

factory_settings["ntp_time_default_levels"] = {
    "ntp_levels" : ntp_default_levels,
    "alert_delay" : (300, 3600),
}



def parse_chrony(info):
    parsed = {}
    for line in info:
        if ":" in line:
            varname, value = " ".join(line).split(":", 1)
            parsed[varname.strip()] = value.strip()
    return parsed

def inventory_chrony(info):
    parsed = parse_chrony(info)
    if parsed:
        return [(None, {})]


def check_chrony(_no_item, params, info):
    parsed = parse_chrony(info)
    if not parsed:
        yield 2, "No status information, chronyd probably not running"
        return

    if type(params) == tuple:
        params = {
            "ntp_levels": params,
            "alert_delay": (300, 3600),
        }
    crit_stratum, warn, crit = params["ntp_levels"]

    offset = float(parsed["System time"].split()[0]) * 1000 # converted to ms
    stratum = int(parsed["Stratum"])

    infotext = "stratum %d" % stratum
    if stratum >= crit_stratum:
        yield 2, infotext + " (maximum allowed is %d)" % (crit_stratum - 1)
    else:
        yield 0, infotext

    status = 0
    infotext = "offset %.4f ms" % offset
    if abs(offset) >= crit:
        status = 2
    elif abs(offset) >= warn:
        status = 1
    if status:
        infotext += " (warn/crit at %.4f/%.4f ms)" % (warn, crit)
    yield status, infotext, [ ("offset", offset, warn, crit, 0, None) ]

    yield 0, "reference: %s" % parsed["Reference ID"]


check_info["chrony"] = {
    'check_function':          check_chrony,
    'inventory_function':      inventory_chrony,
    'service_description':     'NTP Time',
    'has_perfdata':            True,
    'group':                   'ntp_time',
    'default_levels_variable': "ntp_time_default_levels",
}


# /omd/sites/prod/share/check_mk/checks/df.include


filesystem_levels         = [] # obsolete. Just here to check config and warn if changed
filesystem_default_levels = {} # can also be dropped some day in future

inventory_df_exclude_fs            = [ 'tmpfs', 'nfs', 'smbfs', 'cifs', 'iso9660' ]
inventory_df_exclude_mountpoints   = [ '/dev' ]

filesystem_groups = []


factory_settings["filesystem_default_levels"] = {
    "levels"          : (80.0, 90.0), # warn/crit in percent
    "magic_normsize"  : 20,       # Standard size if 20 GB
    "levels_low"      : (50.0, 60.0), # Never move warn level below 50% due to magic factor
    "trend_range"     : 24,
    "trend_perfdata"  : True,    # do send performance data for trends
    "show_levels"     : "onmagic",
    "inodes_levels"   : (10.0, 5.0),
    "show_inodes"     : "onlow",
    "show_reserved"   : False,
}

def df_inventory(mplist):
    group_patterns = {}
    for line in host_extra_conf(g_hostname, filesystem_groups):
        for group_name, pattern in line:
            group_patterns.setdefault(group_name, []).append(pattern)

    inventory = []
    have_groups = set([])
    for mp in mplist:
        in_group = False
        for group_name, patterns in group_patterns.items():
            for pattern in patterns:
                if fnmatch.fnmatch(mp, pattern):
                    have_groups.add(group_name)
                    in_group = True
                    break
        if not in_group:
            inventory.append((mp, {}))

    for group_name in have_groups:
        inventory.append((group_name, { "patterns" : group_patterns[group_name] }))

    return inventory



def get_filesystem_levels(host, mountpoint, size_gb, params):
    mega = 1024 * 1024
    giga = mega * 1024
    levels = factory_settings["filesystem_default_levels"].copy()

    def convert_legacy_levels(value):
        if type(params) == tuple or not params.get("flex_levels"):
            return tuple(map(float, value))
        else:
            return value

    if type(filesystem_default_levels) == dict:
        fs_default_levels = filesystem_default_levels.copy()
        fs_levels = fs_default_levels.get("levels")
        if fs_levels:
            fs_default_levels["levels"] = convert_legacy_levels(fs_levels)
        levels.update(filesystem_default_levels)
    else:
        levels = factory_settings["filesystem_default_levels"].copy()
        levels["levels"] = convert_legacy_levels(filesystem_default_levels[:2])
        if len(filesystem_default_levels) == 2:
            levels["magic"] = None
        else:
            levels["magic"] = filesystem_default_levels[2]

    if type(params) == dict:
        levels.update(params)

    else: # simple format - explicitely override levels and magic
        levels["levels"] = convert_legacy_levels(params[:2])
        if len(params) >= 3:
            levels["magic"] = params[2]

    if type(levels["levels"]) == tuple:
        warn, crit = levels["levels"]
    else:
        found = False
        found_size = 0
        for to_size, this_levels in levels["levels"]:
            if size_gb * giga > to_size and to_size >= found_size:
                warn, crit = this_levels
                found_size = to_size
                found = True
        if not found:
            warn, crit = 100.0, 100.0 # entry not found in list


    magic = levels.get("magic")
    if magic and magic != 1.0:
        if type(warn) != float:
            warn = savefloat(warn * mega / float(size_gb * giga)) * 100
        if type(crit) != float:
            crit = savefloat(crit * mega / float(size_gb * giga)) * 100

        normsize = levels["magic_normsize"]
        hgb_size = size_gb / float(normsize)
        felt_size = hgb_size ** magic
        scale = felt_size / hgb_size
        warn_scaled = 100 - (( 100 - warn ) * scale)
        crit_scaled = 100 - (( 100 - crit ) * scale)

        lowest_warning_level, lowest_critical_level = levels["levels_low"]
        if warn_scaled < lowest_warning_level:
            warn_scaled = lowest_warning_level
        if crit_scaled < lowest_critical_level:
            crit_scaled = lowest_critical_level
    else:
        if type(warn) != float:
            warn_scaled = savefloat(warn * mega / float(size_gb * giga)) * 100
        else:
            warn_scaled = warn

        if type(crit) != float:
            crit_scaled = savefloat(crit * mega / float(size_gb * giga)) * 100
        else:
            crit_scaled = crit

    size_mb     = size_gb * 1024
    warn_mb     = savefloat(size_mb * warn_scaled / 100)
    crit_mb     = savefloat(size_mb * crit_scaled / 100)
    levels["levels_mb"] = (warn_mb, crit_mb)
    if type(warn) == float:
        if warn_scaled < 0 and crit_scaled < 0:
            label = 'warn/crit at free space below'
            warn_scaled *= -1
            crit_scaled *= -1
        else:
            label = 'warn/crit at'
        levels["levels_text"] = "(%s %.2f/%.2f%%)" % (label, warn_scaled, crit_scaled)
    else:
        if warn * mega < 0 and crit * mega < 0:
            label = 'warn/crit at free space below'
            warn *= -1
            crit *= -1
        else:
            label = 'warn/crit at'
        warn_hr = get_bytes_human_readable(warn * mega)
        crit_hr = get_bytes_human_readable(crit * mega)
        levels["levels_text"] = "(%s %s/%s)" % (label, warn_hr, crit_hr)

    if "inodes_levels" in params:
        if type(levels["inodes_levels"]) == tuple:
            warn, crit = levels["inodes_levels"]
        else:
            found = False
            found_size = 0
            for to_size, this_levels in levels["inodes_levels"]:
                if size_gb * giga > to_size and to_size >= found_size:
                    warn, crit = this_levels
                    found_size = to_size
                    found = True
            if not found:
                warn, crit = 100.0, 100.0 # entry not found in list
        levels["inodes_levels"] = warn, crit
    else:
        levels["inodes_levels"] = (None, None)

    return levels

def df_check_filesystem(hostname, mountpoint, size_mb, avail_mb, reserved_mb, params):
    return df_check_filesystem_list(mountpoint, params, [(mountpoint, size_mb, avail_mb, reserved_mb)])

def df_check_filesystem_list(item, params, fslist_blocks, fslist_inodes = None):
    if "patterns" in params:
        patterns = params["patterns"]
        count = 0
        total_size_mb      = 0
        total_avail_mb     = 0
        total_reserved_mb  = 0
        total_inodes       = 0
        total_inodes_avail = 0
        for idx, (mp, size_mb, avail_mb, reserved_mb) in enumerate(fslist_blocks):
            for pattern in patterns:
                if fnmatch.fnmatch(mp, pattern):
                    count += 1
                    total_size_mb     += size_mb
                    total_avail_mb    += avail_mb
                    total_reserved_mb += reserved_mb
                    if fslist_inodes:
                        total_inodes       += fslist_inodes[idx][1]
                        total_inodes_avail += fslist_inodes[idx][2]
                    break
        if count == 0:
            return (3, "No filesystem matching the patterns")
        else:
            status, infotext, perfdata = df_check_filesystem_single(g_hostname, item, total_size_mb, total_avail_mb, total_reserved_mb, total_inodes, total_inodes_avail, params)
            infotext += " (%d filesystems)" % count
            return status, infotext, perfdata
    else:
        for idx, (mp, size_mb, avail_mb, reserved_mb) in enumerate(fslist_blocks):
            if mp == item:
                if fslist_inodes:
                    inodes_total, inodes_avail = fslist_inodes[idx][1], fslist_inodes[idx][2]
                else:
                    inodes_total, inodes_avail = None, None
                return df_check_filesystem_single(g_hostname, mp, size_mb, avail_mb, reserved_mb, inodes_total, inodes_avail, params)
        return (3, "filesystem not found")


def df_check_filesystem_single(hostname, mountpoint, size_mb, avail_mb, reserved_mb, inodes_total, inodes_avail, params, this_time = None):
    if size_mb == 0:
        return (1, "size of filesystem is 0 MB", [])

    used_mb   = size_mb - avail_mb
    used_perc = 100.0 * (float(used_mb) / size_mb)
    size_gb   = size_mb / 1024.0

    levels = get_filesystem_levels(g_hostname, mountpoint, size_gb, params)
    warn_mb, crit_mb       = levels["levels_mb"]
    warn_inode, crit_inode = levels["inodes_levels"]


    used_hr = get_bytes_human_readable(used_mb * 1024 * 1024)
    size_hr = get_bytes_human_readable(size_mb * 1024 * 1024)
    if used_hr[-2:] == size_hr[-2:]:
        used_hr = used_hr[:-3]

    infotext = "%s used (%s of %s)" % (
       get_percent_human_readable(used_perc), used_hr, size_hr)

    if warn_mb < 0.0:
        crit_mb = size_mb + crit_mb
        warn_mb = size_mb + warn_mb

    status = 0
    if used_mb >= crit_mb:
        status = 2
    elif used_mb >= warn_mb:
        status = max(1, status)

    perf_var = mountpoint.replace(" ", "_")
    perfdata = [(perf_var, str(used_mb) + 'MB', warn_mb, crit_mb, 0, size_mb)]
    perfdata.append(('fs_size', str(size_mb) + 'MB'))

    if type(params) == dict:
        show_levels = params.get("show_levels")
        if show_levels == "always" or \
            (show_levels == "onproblem" and status > 0) or \
            (show_levels == "onmagic" and (status > 0 or levels.get("magic", 1.0) != 1.0)):
            infotext += ", " + levels["levels_text"]

        if reserved_mb > 0 and params["show_reserved"]:
            reserved_perc = 100.0 * float(reserved_mb) / size_mb
            infotext += ", therein reserved for root: %.1f%% (%.2f MB)" % (reserved_perc, reserved_mb)
            perfdata.append(("reserved", reserved_mb))



    problems = []

    MB = 1024 * 1024.0
    H24 = 60 * 60 * 24

    if levels.get("trend_range"):
        try:
            range = levels["trend_range"] # in hours
            range_sec = range * 3600.0
            if not this_time:
                this_time = time.time()

            rate = get_rate("df.%s.delta" % mountpoint, this_time, used_mb, allow_negative=True, onwrap=ZERO)
            if levels.get("trend_perfdata"):
                perfdata.append(("growth", rate * H24))

            rate_avg = get_average("df.%s.trend" % mountpoint,
                                   this_time, rate, range_sec / 60.0, True)

            trend = rate_avg * range_sec
            sign = trend > 0 and "+" or ""
            infotext += ", trend: %s%s / %g hours" % \
                        (sign, get_bytes_human_readable(trend * MB), range)

            warn_perf, crit_perf = None, None

            trend_mb = levels.get("trend_mb")
            if trend_mb:
                wa, cr = trend_mb
                warn_perf, crit_perf = wa, cr
                if trend >= wa:
                    problems.append("growing too fast (warn/crit at %s/%s per %.1f h)(!" %
                       ( get_bytes_human_readable(wa * MB), get_bytes_human_readable(cr * MB), range))
                    status = max(1, status)
                    if trend >= cr:
                        status = 2
                        problems[-1] += "!"
                    problems[-1] += ")"
            else:
                wa, cr = None, None

            trend_perc = levels.get("trend_perc")
            if trend_perc:
                wa_perc, cr_perc = trend_perc
                wa = wa_perc / 100.0 * size_mb
                cr = cr_perc / 100.0 * size_mb
                if warn_perf != None:
                    warn_perf = min(warn_perf, wa)
                    crit_perf = min(crit_perf, cr)
                else:
                    warn_perf, crit_perf = wa, cr
                if trend >= wa:
                    problems.append("growing too fast (warn/crit at %.3f%%/%.3f%% per %.1f h)(!" %
                       ( wa_perc, cr_perc, range))
                    status = max(1, status)
                    if trend >= cr:
                        status = 2
                        problems[-1] += "!"
                    problems[-1] += ")"



            hours_left = -1
            if trend > 0:
                space_left = size_mb - used_mb
                hours_left = space_left / trend * range
                timeleft = levels.get("trend_timeleft")
                def format_hours(hours):
                    if hours > 365 * 24:
                        return "more than a year"
                    elif hours > 90 * 24:
                        return "%0d months" % (hours/ (30 * 24))
                    elif hours > 4 * 7 * 24: # 4 weeks
                        return "%0d weeks" % (hours/ (7 * 24))
                    elif hours > 7 * 24:   # 1 week
                        return "%0.1f weeks" % (hours/ (7 * 24))
                    elif hours > 2 * 24:   # 2 days
                        return "%0.1f days" % (hours/24)
                    else:
                        return "%d hours" % hours

                if timeleft:
                    wa, cr = timeleft
                    if hours_left <= cr:
                        status = 2
                        problems.append("only %s until disk full(!!)" % format_hours(hours_left))
                    elif hours_left <= wa:
                        status = max(status, 1)
                        problems.append("only %s until disk full(!)" % format_hours(hours_left))
                    elif hours_left <= wa * 2 or levels.get("trend_showtimeleft"):
                        problems.append("time left until disk full: %s" % format_hours(hours_left))
                elif levels.get("trend_showtimeleft"):
                    problems.append("time left until disk full: %s" % format_hours(hours_left))

            if levels.get("trend_perfdata"):
                perfdata.append(("trend", rate_avg * H24,
                                warn_perf != None and (warn_perf / range_sec * H24) or None,
                                crit_perf != None and (crit_perf / range_sec * H24) or None,
                                0, size_mb / range))

            if levels.get("trend_showtimeleft"):
                perfdata.append(("trend_hoursleft", hours_left))


        except MKCounterWrapped:

            perfdata = []

    if problems:
        infotext += " - %s" % ", ".join(problems)
        problems = []

    inode_status = 0
    if inodes_total:
        inodes_avail_perc = 100.0 * inodes_avail / inodes_total
        inodes_warn, inodes_crit = levels["inodes_levels"]
        if inodes_warn != None:
            if type(inodes_warn) == int:
                if inodes_crit > inodes_avail:
                    inode_status = 2
                    problems.append("less than %dk inodes available(!!)" % (crit_inode / 1000))
                elif inodes_warn > inodes_avail:
                    inode_status = 1
                    problems.append("less than %dk inodes available(!)" % (warn_inode / 1000))
                inodes_warn_abs = inodes_warn
                inodes_crit_abs = inodes_crit

            else:
                if inodes_crit > inodes_avail_perc:
                    inode_status = 2
                    problems.append("less than %0.2f%% inodes available(!!)" % inodes_crit)
                elif inodes_warn > inodes_avail_perc:
                    inode_status = 1
                    problems.append("less than %.02f%% inodes available(!)" % inodes_warn)
                inodes_warn_abs = (100 - inodes_warn) / 100.0 * inodes_total
                inodes_crit_abs = (100 - inodes_crit) / 100.0 * inodes_total

        else:
            inodes_warn_abs = None
            inodes_crit_abs = None

        status = max(status, inode_status)
        show_inodes = levels["show_inodes"]
        if show_inodes == "always" or \
            (show_inodes == "onlow" and (inode_status or inodes_avail_perc < 50)) or \
            (show_inodes == "onproblem" and inode_status):
            infotext += ", inodes available: %dk/%0.2f%%" % (inodes_avail / 1000, inodes_avail_perc)

        perfdata += [ ("inodes_used", inodes_total - inodes_avail, inodes_warn_abs, inodes_crit_abs, 0, inodes_total) ]

    if problems:
        infotext += " - %s" % ", ".join(problems)
        problems = []

    return (status, infotext, perfdata)


# /omd/sites/prod/share/check_mk/checks/df





def df_parse_info(info):
    df_blocks = []
    df_inodes = []
    btrfs_devices = set() # We might generalize that later
    lines = iter(info)

    try:
        is_inode = False
        while True:
            line = lines.next()
            if line[-1] == '[df_inodes_start]':
                is_inode = True
                continue
            elif line[-1] == '[df_inodes_end]':
                is_inode = False
                continue
            if not is_inode:
                if line[2] == "File" and line[3] == "System":
                    line =  [ line[0], " ".join(line[1:4]) ] + line[4:]
                if line[1] == "btrfs":
                    device = line[0]
                    if device not in btrfs_devices:
                        btrfs_devices.add(device)
                        df_blocks.append(line[:6] + [ "btrfs " + line[0] ]) # replace mount point with device
                else:
                    df_blocks.append(line)
            else:
                df_inodes.append(line)
    except StopIteration:
        pass

    return df_blocks, df_inodes

def inventory_df(info):
    df_blocks, df_inodes = df_parse_info(info)
    mplist = []
    for line in df_blocks:
        if line[1] in inventory_df_exclude_fs:
            continue # ignore this filesystem type

        if line[2] == '-' or int(line[2]) == 0 or line[5] == '-':
            continue # exclude filesystems without size

        mountpoint = " ".join(line[6:]).replace('\\', '/') # Windows \ is replaced with /
        if mountpoint in inventory_df_exclude_mountpoints:
            continue # exclude this mount point (/tmp, /proc, whatever user wants)

        mplist.append(mountpoint)

    return df_inventory(mplist)


def check_df(item, params, info):
    fslist_blocks = []
    fslist_inodes = []
    df_blocks, df_inodes = df_parse_info(info)
    for idx, line in enumerate(df_blocks):
        mountpoint = " ".join(line[6:]).replace('\\', '/')
        if "patterns" in params or item == mountpoint:
            size_mb    = int(line[2]) / 1024.0
            avail_mb   = int(line[4]) / 1024.0
            used_mb    = int(line[3]) / 1024.0
            reserved_mb = size_mb - avail_mb - used_mb # reserved for root
            fslist_blocks.append((mountpoint, size_mb, avail_mb, reserved_mb))
            if df_inodes and len(df_inodes) > idx:
                fslist_inodes.append((mountpoint, int(df_inodes[idx][2]), int(df_inodes[idx][4])))
    return df_check_filesystem_list(item, params, fslist_blocks, fslist_inodes)

check_info['df'] = {
    "check_function"          : check_df,
    "inventory_function"      : inventory_df,
    "service_description"     : "Filesystem %s",
    "has_perfdata"            : True,
    "group"                   : "filesystem",
    "default_levels_variable" : "filesystem_default_levels",
    "includes"                : [ "df.include" ],
}


# /omd/sites/prod/share/check_mk/checks/ipmi_sensors




def inventory_freeipmi(info):
    return [ (line[1], "", None) for line in info
             if not ( line[-1] in ['[Unknown]', '[NA]'] or
                      "_=_" in line[-1] )]


def check_freeipmi(item, _no_params, info):
    for line in info:
        if line[1] == item:
            status = line[-1][1:-1]
            perfdata = []
            infotext = "Sensor status is " + status

            if len(line) == 4:
                current, levels = line[2].split('(')

                cparts = current.split("_")
                if cparts[0] == "NA":
                    current = None
                else:
                    current = float(cparts[0])
                    if len(cparts) > 1:
                        unit = " " + cparts[1]
                    else:
                        unit = ""

                    lower, upper = levels[:-1].split("/")
                    if lower == "NA" and upper != "NA":
                        crit = upper
                        levelstext = ", critical at %.1f%s" % (float(upper), unit)
                    elif lower != "NA" and upper == "NA":
                        crit = lower
                        levelstext = ", critical below %.1f%s" % (float(lower), unit)
                    elif lower != "NA" and upper != "NA":
                        crit = upper
                        levelstext = ", valid range is %.1f%s ... %.1f%s" % \
                                      (float(lower), unit, float(upper), unit)
                    else:
                        crit = None
                        levelstext = ""

                    if "temperature" in item.lower():
                        perfdata = [ ("value", current, None, crit) ]
                    else:
                        perfdata = []

                    infotext = "Current value %.1f%s%s" % (current, unit, levelstext)

            if status in [ "OK", "Entity_Present", "battery_presence_detected",
                           "Drive_Presence", "transition_to_Running", "Device_Enabled" ] or \
               status.startswith("Fully_Redundant") or \
               status.endswith("is_connected") or \
               status.endswith("Presence_detected") or \
               status.endswith("Device_Present"):
                return (0, infotext, perfdata)

            else:
                return (2, infotext, perfdata)

    return (3, "item %s not found" % item)


check_info["ipmi_sensors"] = {
    'check_function':          check_freeipmi,
    'inventory_function':      inventory_freeipmi,
    'service_description':     'IPMI Sensor %s',
    'has_perfdata':            True,
}


# /omd/sites/prod/share/check_mk/checks/cpu_load.include


def check_cpu_load_generic(params, load, num_cpus=1):
    if type(params) == tuple:
        warn, crit = [ p*num_cpus for p in params ]
    else:
        warn, crit = None, None

    perfdata = [ ('load' + str(z), l, warn, crit, 0, num_cpus )
                 for (z,l) in [ (1,load[0]), (5,load[1]), (15, load[2]) ] ]

    state, text, perf = check_levels(load[2], 'load15', params, factor = num_cpus)
    perfdata += perf
    infotext = "15 min load %.2f" % load[2]
    if num_cpus > 1:
        infotext += " at %d Cores (%.2f per Core)" % (num_cpus, load[2]/num_cpus)
    if text:
        infotext += ", " + text
    return state, infotext, perfdata


# /omd/sites/prod/share/check_mk/checks/cpu





cpuload_default_levels = (5.0, 10.0)

def inventory_cpu_load(info):
    if len(info) == 1 and len(info[0]) >= 5:
        return [(None, "cpuload_default_levels")]


def check_cpu_load(item, params, info):
    if not info:
        return

    if len(info[0]) >= 6:
        line = " ".join(info[0])
        if "lcpu=" in line:
            for part in info[0]:
                if "lcpu=" in part:
                    num_cpus = int(part.split("=", 1)[1])
                    break
        else:
            num_cpus = int(info[0][5])
    else:
        num_cpus = 1

    load = map(float, info[0][0:3])
    return check_cpu_load_generic(params, load, num_cpus)


check_info["cpu.loads"] = {
    "check_function"          : check_cpu_load,
    "inventory_function"      : inventory_cpu_load,
    "service_description"     : "CPU load",
    "has_perfdata"            : True,
    "group"                   : "cpu_load",
    "includes"                : ["cpu_load.include"],
    "handle_real_time_checks" : True,
}



threads_default_levels = (2000, 4000)

def inventory_cpu_threads(info):
    if len(info) == 1 and len(info[0]) >= 5:
        return [(None, "", "threads_default_levels")]

def check_cpu_threads(item, params, info):
    try:
        nthreads = int(info[0][3].split('/')[1])
    except:
        return (3, "invalid output from plugin")
    warn, crit = params
    perfdata = [('threads', nthreads, warn, crit, 0 )]
    if nthreads >= crit:
        return (2, "%d threads (critical at %d)" % (nthreads, crit), perfdata)
    elif nthreads >= warn:
        return (1, "%d threads (warning at %d)" % (nthreads, warn), perfdata)
    else:
        return (0, "%d threads" % (nthreads,), perfdata)


check_info["cpu.threads"] = {
    "check_function"          : check_cpu_threads,
    "inventory_function"      : inventory_cpu_threads,
    "service_description"     : "Number of threads",
    "has_perfdata"            : True,
    "group"                   : "threads",
    "handle_real_time_checks" : True,
}



# /omd/sites/prod/share/check_mk/checks/diskstat.include

diskstat_inventory_mode = "rule" # "summary", "single", "legacy"

diskstat_default_levels = {
}

diskstat_inventory = []


def inventory_diskstat_generic(info):
    if not info:
        return

    if diskstat_inventory_mode == "rule":
        hits = host_extra_conf(g_hostname, diskstat_inventory)
        if len(hits) > 0:
            modes = hits[0]
        else:
            modes = [ "summary" ]

    elif diskstat_inventory_mode == "single":
        modes = [ "physical" ]
    elif diskstat_inventory_mode == "summary":
        modes = [ "summary" ]
    else:
        modes = [ "legacy" ]

    inventory = []
    if "summary" in modes:
        inventory.append( ( "SUMMARY", "diskstat_default_levels" ) )

    if "legacy" in modes:
        inventory += [ ( "read", None ), ( "write", None ) ]

    if "physical" in modes:
        inventory += [ (line[1], "diskstat_default_levels")
                       for line in info
                       if not ' ' in line[1] ]

    if "lvm" in modes:
        inventory += [ (line[1], "diskstat_default_levels")
                       for line in info
                       if line[1].startswith("LVM ") ]

    if "vxvm" in modes:
        inventory += [ (line[1], "diskstat_default_levels")
                       for line in info
                       if line[1].startswith("VxVM ") ]

    return inventory



def check_diskstat_line(this_time, item, params, line, mode='sectors'):
    average_range = params.get("average")
    if average_range == 0:
        average_range = None # disable averaging when 0 is set

    perfdata = []
    infos = []
    status = 0
    node = line[0]
    if node != None and node != "":
        infos.append("Node %s" % node)
    prediction_perf = []
    for what, ctr in [ ("read",  line[2]), ("write", line[3]) ]:
        if node:
            countername = "diskstat.%s.%s.%s" % (node, item, what)
        else:
            countername = "diskstat.%s.%s" % (item, what)

        levels = params.get(what)
        if type(levels) == tuple:
            warn, crit = levels
        else:
            warn, crit = None, None

        per_sec = get_rate(countername, this_time, int(ctr))
        if mode == 'sectors':
            bytes_per_sec = per_sec * 512
        elif mode == 'bytes':
            bytes_per_sec = per_sec

        infos.append("%s/sec %s" % (get_bytes_human_readable(bytes_per_sec), what))
        perfdata.append( (what, bytes_per_sec, warn, crit) )
        dsname = what

        if average_range != None:
            avg = get_average(countername + ".avg", this_time, bytes_per_sec, average_range)
            dsname = what + ".avg"
            perfdata.append( (dsname, avg) )
            bytes_per_sec = avg

        state, text, extraperf = check_levels(bytes_per_sec, dsname, levels,
                                              unit = "MB/s", scale = 1048576, statemarkers=True)
        if text:
            infos.append(text)
        status = max(state, status)
        prediction_perf += extraperf

    if average_range != None:
        perfdata = [ perfdata[0], perfdata[2], perfdata[1], perfdata[3] ]

    ios_per_sec = None
    if len(line) >= 6 and line[4] >= 0 and line[5] > 0:
        reads, writes = map(int, line[4:6])
        ios = reads + writes
        ios_per_sec = get_rate(countername + ".ios", this_time, ios)
        infos.append("IOs: %.2f/sec" % ios_per_sec)

        if params.get("latency_perfdata"):
            perfdata.append(("ios", ios_per_sec))

    if len(line) >= 7 and line[6] >= 0:
        timems = int(line[6])
        timems_per_sec = get_rate(countername + ".time", this_time, timems)
        if not ios_per_sec:
            latency = 0.0
        else:
            latency = timems_per_sec / ios_per_sec
        infos.append("Latency: %.2fms" % latency)
        if "latency" in params:
            warn, crit = params["latency"]
            if latency >= crit:
                status = 2
                infos[-1] += "(!!)"
            elif latency >= warn:
                status = max(status, 1)
                infos[-1] += "(!)"
        else:
            warn, crit = None, None

        if params.get("latency_perfdata"):
            perfdata.append(("latency", latency, warn, crit))

    if len(line) >= 9:
        for what, ctr in [ ("read",  line[7]), ("write", line[8]) ]:
            countername = "diskstat.%s.ql.%s" % (item, what)
            levels = params.get(what + "_ql")
            if levels:
                warn, crit = levels
            else:
                warn, crit = None, None

            qlx = get_rate(countername, this_time, int(ctr))
            ql = qlx / 10000000.0
            infos.append(what.title() + " Queue: %.2f" % ql)

            if levels != None:
                if ql >= crit:
                    status = 2
                    infos[-1] += "(!!)"
                elif ql >= warn:
                    status = max(status, 1)
                    infos[-1] += "(!)"

            if params.get("ql_perfdata"):
                perfdata.append((what + "_ql", ql))

    perfdata += prediction_perf

    return (status, ", ".join(infos) , perfdata)


def check_diskstat_generic(item, params, this_time, info, mode='sectors'):
    if item in [ 'read', 'write' ]:
        return check_diskstat_old(item, params, this_time, info)


    summed_up = [0] * 13
    matching = 0

    for line in info:
        if item == 'SUMMARY' and line[0] != None:
            return 3, "summary mode not supported in a cluster"

        elif item == 'SUMMARY' and ' ' in line[1]:
            continue # skip non-physical disks

        elif item == 'SUMMARY' or line[1] == item:
            matching += 1
            summed_up = map(lambda e: e[0] + int(e[1]), zip(summed_up, line[2:]))

    if matching == 0:
        return 3, "No matching disk found"
    else:
        return check_diskstat_line(this_time, item, params, [None, ''] + summed_up, mode)


def check_diskstat_old(item, params, this_time, info):
    if item == 'read':
        index = 2 # sectors read
    elif item == 'write':
        index = 3 # sectors written
    else:
        return (3, "invalid item %s" % (item,))

    this_val = 0
    for line in info:
        if line[0] != None:
            return 3, "read/write mode not supported in a cluster"
        if ' ' not in line[1]:
            this_val += int(line[index])

    per_sec = get_rate("diskstat." + item, this_time, this_val)
    mb_per_s = per_sec / 2048.0    # Diskstat output is in sectors a 512 Byte
    kb_per_s = per_sec / 2.0
    perfdata = [ (item, "%f" % kb_per_s ) ]
    return (0, "%.1f MB/s" % mb_per_s, perfdata)



def diskstat_select_disk(disks, item):


    if item == "SUMMARY":
        summarized = {
            "node"                       : None,
        }

        if disks:
            num_averaged = 0
            for device, disk in disks.items():
                for key in disk.keys():
                    if key != "node":
                        summarized.setdefault(key, 0.0)

                if device.startswith("LVM "):
                    continue # skip LVM devices for summary

                if True or disk["read_throughput"] + disk["write_throughput"] > 0: # skip idle disks
                    num_averaged += 1
                    for key, value in disk.items():
                        if key != "node":
                            summarized[key] += value

            if num_averaged:
                for key, value in summarized.items():
                    if key.startswith("ave") or key in ("utilization", "latency", "queue_length"):
                        summarized[key] /= num_averaged

        return summarized

    elif item not in disks:
        return None

    else:
        return disks[item]

def check_diskstat_dict(item, params, disks):
    if item in ("read", "write"):
        yield 3, "Sorry, the new version of this check does not " \
                  "support one service for read and one for write anymore."
        return

    this_time = time.time()
    disk = diskstat_select_disk(disks, item)
    if not disk:
        return

    prefix = ""
    averaging = params.get("average") # in seconds here!
    if averaging:
        avg_disk = {} # Do not modify our arguments!!
        for key, value in disk.items():
            if type(value) in (int, float):
                avg_disk[key] = get_average("diskstat.%s.%s.avg" % (item, key), this_time, value, averaging / 60.0)
            else:
                avg_disk[key] = value
        disk = avg_disk
        prefix = "%s average: " % get_age_human_readable(averaging)


    if "utilization" in disk:
        util = disk["utilization"]
        state, text, extraperf = check_levels(util, "disk_utilization", params.get("utilization"),
                                              unit = "%", scale = 0.01, statemarkers=False)
        yield state, "%sUtilization: %.1f%%%s" % (prefix, util * 100, text), extraperf


    for what in "read", "write":
        if what + "_throughput" in disk:
            throughput = disk[what + "_throughput"]
            state, text, extraperf = check_levels(throughput, "disk_" + what + "_throughput", params.get(what),
                                                  unit = "MB/s", scale = 1048576, statemarkers=False)
            yield state, "%s: %s/s%s" % (what.title(), get_bytes_human_readable(throughput), text), extraperf


    for what in [ "wait", "read_wait", "write_wait"]:
        if "average_" + what in disk:
            wait = disk["average_" + what]
            state, text, extraperf = check_levels(wait, what, params.get(what),
                                                  unit = "ms", scale = 0.001, statemarkers=False)
            yield state, "Average %s: %.2f ms%s" % (what.title().replace("_", " "), wait * 1000, text), extraperf

    if "latency" in disk:
        latency = disk["latency"]
        state, text, extraperf = check_levels(latency, "disk_latency", params.get("latency"),
                                              unit = "ms", scale = 0.001, statemarkers=False)
        yield state, "Latency: %.2f ms%s" % (latency * 1000.0, text), extraperf


    perfdata = []
    for key in sorted(disk.keys()):
        value = disk[key]
        if type(value) in (int, float):
            perfdata.append(("disk_" + key, value))

    yield 0, None, perfdata


# /omd/sites/prod/share/check_mk/checks/diskstat






def parse_diskstat(info):
    timestamp_str, proc_diskstat, name_info = diskstat_extract_name_info(info)
    timestamp = int(timestamp_str)

    disks = {}

    for node_name, major, minor, device, \
        read_ios, read_merges, read_sectors, read_ticks, \
        write_ios, write_merges, write_sectors, write_ticks, \
        ios_in_prog, total_ticks, rq_ticks in proc_diskstat:

        if (node_name, int(major), int(minor)) in name_info:
            device = name_info[(node_name, int(major), int(minor))]

        counter_base = "diskstat.%s." % device


        read_ticks_rate  = get_rate(counter_base + "read_ticks",   timestamp, int(read_ticks), onwrap=0.0)
        write_ticks_rate = get_rate(counter_base + "write_ticks",  timestamp, int(write_ticks), onwrap=0.0)
        total_ticks_rate = get_rate(counter_base + "total_ticks",  timestamp, int(total_ticks), onwrap=0.0)
        read_ios_rate    = get_rate(counter_base + "read_ios",     timestamp, int(read_ios), onwrap=0.0)
        write_ios_rate   = get_rate(counter_base + "write_ios",    timestamp, int(write_ios), onwrap=0.0)
        total_ios_rate   = read_ios_rate + write_ios_rate
        utilization      = total_ticks_rate / 1000 # not percent, but 0...1
        read_bytes_rate  = get_rate(counter_base + "read_sectors",  timestamp, int(read_sectors), onwrap=0.0) * 512
        write_bytes_rate = get_rate(counter_base + "write_sectors", timestamp, int(write_sectors), onwrap=0.0) * 512
        total_bytes_rate = read_bytes_rate + write_bytes_rate

        if total_ios_rate:
            latency              = utilization / total_ios_rate
            average_wait         = (read_ticks_rate + write_ticks_rate) / total_ios_rate / 1000.0
            average_request_size = total_bytes_rate / total_ios_rate
        else:
            latency              = 0.0
            average_wait         = 0.0
            average_request_size = 0.0

        if read_ticks_rate and read_ios_rate > 0:
            average_read_wait = read_ticks_rate / read_ios_rate / 1000.0
            average_read_size = read_bytes_rate / read_ios_rate
        else:
            average_read_wait = 0.0
            average_read_size = 0.0

        if write_ticks_rate and write_ios_rate > 0:
            average_write_wait = write_ticks_rate / write_ios_rate / 1000.0
            average_write_size = write_bytes_rate / write_ios_rate
        else:
            average_write_wait = 0.0
            average_write_size = 0.0

        disks[device] = {
            "node"                       : node_name,
            "read_ios"                   : read_ios_rate,
            "write_ios"                  : write_ios_rate,
            "read_throughput"            : read_bytes_rate,
            "write_throughput"           : write_bytes_rate,
            "utilization"                : utilization,
            "latency"                    : latency,
            "average_request_size"       : average_request_size,
            "average_wait"               : average_wait,
            "average_read_wait"          : average_read_wait,
            "average_read_request_size"  : average_read_size,
            "average_write_wait"         : average_write_wait,
            "average_write_request_size" : average_write_size,
            "queue_length"               : int(ios_in_prog),
        }

    return disks




def diskstat_extract_name_info(info):
    disks = {}
    name_info = {} # dict from (node, major, minor) to itemname
    timestamp = None

    info_plain = []
    phase = 'info'
    node = None
    for line in info:
        if node == None:
            node = line[0]
        if line[1] == '[dmsetup_info]':
            phase = 'dmsetup_info'
        elif line[1] == '[vx_dsk]':
            phase = 'vx_dsk'
        elif line[0] != node:
            phase = 'info'
            node = line[0]
        else:
            if phase == 'info':
                if len(line) == 2:
                    timestamp = int(line[1])
                else:
                    info_plain.append(line)
            elif phase == 'dmsetup_info':
                try:
                    major, minor = map(int, line[2].split(':'))
                    if len(line) == 5:
                        name = "LVM %s" % line[1]
                    else:
                        name = "DM %s" % line[1]
                    name_info[node, major, minor] = name
                except:
                    pass # ignore such crap as "No Devices Found"
            elif phase == 'vx_dsk':
                major = int(line[1], 16)
                minor = int(line[2], 16)
                group, disk = line[3].split('/')[-2:]
                name = "VxVM %s-%s" % (group, disk)
                name_info[(node, major, minor)] = name

    return timestamp, info_plain, name_info

def diskstat_convert_info(info):
    disks, multipath_info = info
    converted_disks = dict(disks.items()) # we must not mody info!

    if multipath_info:
        for uuid, multipath in multipath_info.items():
            if "alias" not in multipath:
                multipath["alias"] = ""

            if multipath["device"] in converted_disks or \
               "DM %s" % multipath["alias"] in converted_disks:
                for path in multipath["paths"]:
                    if path in converted_disks:
                        del converted_disks[path]

            if multipath["device"] in converted_disks:
                converted_disks[uuid] = converted_disks[multipath["device"]]
                del converted_disks[multipath["device"]]

            if "DM %s" % multipath["alias"] in converted_disks:
                alias = "DM %s" % multipath["alias"]
                converted_disks[uuid] = converted_disks[alias]
                del converted_disks[alias]

    for device in converted_disks.keys():
        if device.startswith("dm-"):
            del converted_disks[device]

    return converted_disks


def inventory_diskstat(info):
    converted_disks = diskstat_convert_info(info)

    return inventory_diskstat_generic([
        (disk["node"], device) for device, disk in converted_disks.items()])


def check_diskstat(item, params, info):
    return check_diskstat_dict(item, params, diskstat_convert_info(info))


check_info["diskstat"] = {
    'parse_function'      : parse_diskstat,
    'inventory_function'  : inventory_diskstat,
    'check_function'      : check_diskstat,
    'service_description' : 'Disk IO %s',
    'has_perfdata'        : True,
    'group'               : 'diskstat',
    "node_info"           : True, # add first column with actual host name
    'includes'            : [ "diskstat.include" ],
    'extra_sections'      : [ "multipath" ],
}



# /omd/sites/prod/share/check_mk/checks/logins



logins_default_levels = (20,30)

def inventory_logins(info):
    if info:
        return [ (None, "logins_default_levels") ]

def check_logins(_no_item, params, info):
    if info:
        logins = int(info[0][0])
        warn, crit = params
        state = 0
        if logins >= crit:
            state = 2
        elif logins >= warn:
            state = 1

        infotext = "%d logins on system (warn/crit at %d/%d)" % ( logins, warn, crit )
        perfdata = [ ( "logins", logins, warn, crit, 0 ) ]
        yield state, infotext, perfdata


check_info["logins"] = {
    'check_function'      : check_logins,
    'inventory_function'  : inventory_logins,
    'service_description' : 'Logins',
    'has_perfdata'        : True,
    'group'               : 'logins',
}


# /omd/sites/prod/share/check_mk/checks/postfix_mailq



factory_settings['postfix_mailq_default_levels'] = {
    "deferred" : (10, 20),
    "active"   : (200, 300), # may become large for big mailservers
}

def inventory_postfix_mailq(info):
    if len(info) > 0 and info[0] != '':
        return [(None, {})]

def postfix_mailq_to_bytes(value, uom):
    uom = uom.lower()
    if uom == 'kbytes':
        return value * 1024
    elif uom == 'mbytes':
        return value * 1024 * 1024
    elif uom == 'gbytes':
        return value * 1024 * 1024 * 1024

def check_postfix_mailq(_no_item, params, info):
    if type(params) != dict:
        params = {
            "deferred" : params,
        }
    for line in info:
        state = 0
        if line[0].startswith("QUEUE_"):
            queue = line[0].split("_")[1]

            if len(line) == 2:
                size   = 0
                length = int(line[1]) # number of mails
            else:
                size   = int(line[1]) # in bytes
                length = int(line[2]) # number of mails
            infotext = "%s queue length is %d" % (queue, length)
            if queue == "deferred":
                length_var = "length"
                size_var = "size"
            else:
                length_var = "mail_queue_%s_length" % queue
                size_var = "mail_queue_%s_size" % queue
            if queue in params:
                warn, crit = params[queue]
                if length >= crit:
                    state = 2
                elif length >= warn:
                    state = 1
                if state:
                    infotext += " (Levels at %d/%d)" % (warn, crit)
                perfdata = [ (length_var, length, warn, crit) ]
            else:
                perfdata = [ (length_var, length) ]

            perfdata.append((size_var, size))

            yield state, infotext, perfdata

        elif " ".join(line[-2:]) == 'is empty':
            warn, crit = params["deferred"]
            infotext = 'The mailqueue is empty'
            perfdata = [ ('length', 0, warn, crit),
                         ('size', 0) ]
            yield 0, infotext, perfdata

        elif line[0] == '--' or line[0:2] == [ 'Total', 'requests:']:
            warn, crit = params["deferred"]
            if line[0] == '--':
                size    = postfix_mailq_to_bytes(float(line[1]), line[2])
                length  = int(line[4])
            else:
                size    = 0
                length  = int(line[2])

            infotext = 'Mailqueue length is %d' % length
            perfdata = [ ('length', length, warn, crit),
                         ('size', size) ]

            if length >= crit:
                state = 2
            elif length >= warn:
                state = 1
            if state:
                infotext += " (warn/crit at %d/%d)" % (warn, crit)

            yield state, infotext, perfdata

check_info["postfix_mailq"] = {
    'check_function'          : check_postfix_mailq,
    'inventory_function'      : inventory_postfix_mailq,
    'service_description'     : 'Postfix Queue',
    'default_levels_variable' : 'postfix_mailq_default_levels',
    'group'                   : 'mailqueue_length',
    'has_perfdata'            : True,
}


# /omd/sites/prod/share/check_mk/checks/mounts


def inventory_mounts(info):
    inventory = []
    devices = []
    for dev, mp, fstype, options, dump, fsck in info:
        if fstype not in [ 'tmpfs' ] and dev not in devices:
            devices.append(dev)
            opts = options.split(",")
            opts.sort()
            inventory.append( (mp, opts) )
    return inventory

def check_mounts(item, targetopts, info):

    def should_ignore_option(option):
        for ignored_option in [ "commit=", "localalloc=", "subvol=", "subvolid=" ]:
            if option.startswith(ignored_option):
                return True
        return False

    for dev, mp, fstype, options, dump, fsck in info:
        if item == mp:
            opts = options.split(",")

            exceeding = []
            for o in opts:
                if o not in targetopts and not should_ignore_option(o):
                    exceeding.append(o)

            missing = []
            for o in targetopts:
                if o not in opts and not should_ignore_option(o):
                    missing.append(o)

            if not missing and not exceeding:
                return (0, "mount options exactly as expected")

            infos = []
            if missing:
                infos.append("missing: %s" % ",".join(missing))
            if exceeding:
                infos.append("exceeding: %s" % ",".join(exceeding))
            infotext = ", ".join(infos)

            if "ro" in exceeding:
                return (2, "filesystem has switched to read-only "
                           "and is probably corrupted(!!), " + infotext)

            return (1, infotext)

    return (3, "filesystem not mounted")



check_info["mounts"] = {
    'check_function':          check_mounts,
    'inventory_function':      inventory_mounts,
    'service_description':     'Mount options of %s',
    'group':                   'fs_mount_options',
}


# /omd/sites/prod/share/check_mk/checks/tcp_connections.include

tcp_conn_stats_default_levels = {}

tcp_connections_state_map = [
    ("ESTABLISHED",  1),    # connection up and passing data
    ("SYN_SENT",     2),    # session has been requested by us; waiting for reply from remote endpoint
    ("SYN_RECV",     3),    # session has been requested by a remote endpoint for a socket on which we were listening
    ("LAST_ACK",     9),    # our socket is closed; remote endpoint has also shut down; we are waiting for a final acknowledgement
    ("CLOSE_WAIT",   8),    # remote endpoint has shut down; the kernel is waiting for the application to close the socket
    ("TIME_WAIT",    6),    # socket is waiting after closing for any packets left on the network
    ("CLOSED",       7),    # socket is not being used (FIXME. What does mean?)
    ("CLOSING",      11),   # our socket is shut down; remote endpoint is shut down; not all data has been sent
    ("FIN_WAIT1",    4),    # our socket has closed; we are in the process of tearing down the connection
    ("FIN_WAIT2",    5),    # the connection has been closed; our socket is waiting for the remote endpoint to shut down
    ("LISTEN",       10),   # represents waiting for a connection request from any remote TCP and port
    ("BOUND",        None), # Socket did a bound() but TCP stack not yet active (Solaris)
    ("IDLE",         None), # TCP endpoints are in IDLE state when first created
]



def inventory_tcp_connections(parsed):
    if len(parsed) > 0:
        return [ (None, 'tcp_conn_stats_default_levels') ]


def check_tcp_connections(item, params, parsed):
    hit = False
    for tcp_state_readable, tcp_state_int_str in tcp_connections_state_map:
        num = parsed.get(tcp_state_readable, \
                   parsed.get(tcp_state_int_str, 0))
        state = 0
        perf = [tcp_state_readable, num]
        if num > 0: # Only check positive counts
            hit = True
            infotext = "%s: %d" % (tcp_state_readable, num)
            levels = params.get(tcp_state_readable)
            if levels:
                warn, crit = levels
                perf.append(warn)
                perf.append(crit)
                if num >= crit:
                    state = 2
                elif num >= warn:
                    state = 1
                if state > 0:
                    infotext += " (warn/crit at %d/%d)" % (warn, crit)
            yield state, infotext, [ tuple(perf) ]
        else:
            yield 0, None, [ tuple(perf) ]

    if not hit:
        yield 0, "Currently no TCP connections"



# /omd/sites/prod/share/check_mk/checks/tcp_conn_stats




def parse_tcp_conn_stats(info):
    parsed = {}
    for tcp_state, tcp_count in info:
        if len(tcp_state) == 2:
            tcp_state = int(tcp_state, 16) # Hex
        parsed[tcp_state] = int(tcp_count)
    return parsed


check_info["tcp_conn_stats"] = {
    'parse_function'        : parse_tcp_conn_stats,
    'check_function'        : check_tcp_connections,
    'inventory_function'    : inventory_tcp_connections,
    'service_description'   : 'TCP Connections',
    'has_perfdata'          : True,
    'group'                 : 'tcp_conn_stats',
    'includes'              : [ "tcp_connections.include" ],
}


# /omd/sites/prod/share/check_mk/checks/multipath

inventory_multipath_rules = []















def parse_multipath(info):
    reg_headers = [
        (regex(r"^[0-9a-z]{33}$"),                                0, None, None), # 1. (should be included in 3.)
        (regex(r"^([^\s]+)\s\(([0-9A-Za-z_-]+)\)\s(dm.[0-9]+)"),  2, 1,    3),    # 2.
        (regex(r"^([^\s]+)\s\(([0-9A-Za-z_-]+)\)"),               2, 1,    None),    # 2.
        (regex(r"^[a-zA-Z0-9_]+$"),                               0, None, None), # 3.
        (regex(r"^([0-9a-z]{33}|[0-9a-z]{49})\s?(dm.[0-9]+).*$"), 1, None, 2), # 4.
        (regex(r"^[a-zA-Z0-9_]+(dm-[0-9]+).*$"),                  0, None, 1), # 5. Remove this line in 1.2.0
        (regex(r"^([-a-zA-Z0-9_ ]+)\s?(dm-[0-9]+).*$"),           1, None, 2), # 6. and 7.
    ]

    reg_prio = regex("[[ ]prio=")
    reg_lun  = regex("[0-9]+:[0-9]+:[0-9]+:[0-9]+")
    uuid = None
    alias = None
    groups = {}
    group = {}
    numpaths = None
    for line in info:
        if line[0] == "multipath.conf":
            continue

        if line[0] == "dm":
            uuid = None
            continue

        l = " ".join(line)

        if l.endswith('kernel driver not loaded') \
           or l.endswith('does not exist, blacklisting all devices.') \
           or l.endswith('A sample multipath.conf file is located at') \
           or l.endswith('multipath.conf'):
            uuid = None
            continue

        if line[0][0] not in [ '[', '`', '|', '\\' ] and not line[0].startswith("size="):
            matchobject = None
            for header_regex, uuid_pos, alias_pos, dm_pos in reg_headers:
                matchobject = header_regex.search(l)

                if matchobject:
                    uuid = matchobject.group(uuid_pos).strip()

                    if alias_pos:
                        alias = matchobject.group(alias_pos)
                    else:
                        alias = None

                    if dm_pos:
                        dm_device = matchobject.group(dm_pos)
                    else:
                        dm_device = None

                    break

            if not matchobject:
                raise Exception("Invalid line in agent output: " + l)

            numpaths = 0
            lun_info = []
            paths_info = []
            broken_paths = []
            group = {}
            group['paths'] = paths_info
            group['broken_paths'] = broken_paths
            group['luns'] = lun_info
            group['uuid'] = uuid
            group['state'] = None
            group['numpaths'] = 0
            group['device'] = dm_device
            groups[uuid] = group

            if alias:
                group['alias'] = alias

            continue
        else:
            if uuid != None:
                if line[0] == '|':
                    line = line[1:]
                if reg_prio.search(l):
                    group['state'] = "".join(line[3:])
                elif len(line) >= 4 and reg_lun.match(line[1]):
                    luninfo = "%s(%s)" % (line[1], line[2])
                    lun_info.append(luninfo)
                    state = line[4]
                    if not "active" in state:
                        broken_paths.append(luninfo)
                    numpaths += 1
                    group['numpaths'] = numpaths
                    paths_info.append(line[2])
    return groups

def inventory_multipath(parsed):
    settings = host_extra_conf_merged(g_hostname, inventory_multipath_rules)

    inventory = []
    for uuid, info in parsed.items():
        if "alias" in info and settings.get("use_alias"):
            item = info["alias"]
        else:
            item = uuid
        inventory.append( (item, info['numpaths']) )
    return inventory

def check_multipath(item, target_numpaths, parsed):
    if item in parsed:
        mmap = parsed[item]
    elif item.strip() in parsed:
        mmap = parsed[item.strip()]
    else:
        for mmap in parsed.values():
            if mmap.get("alias") == item:
                break
        else:
            return 3, "Multipath device not found in agent output"

    alias = mmap.get('alias')
    uuid = mmap.get('uuid')

    if item == uuid and alias:
        aliasinfo = "(%s) " % alias
    elif item == alias and uuid:
        aliasinfo = "(%s) " % uuid
    else:
        aliasinfo = ""

    numpaths = mmap['numpaths']
    broken = mmap['broken_paths']
    numbroken = len(broken)
    if numbroken > 0:
        return (2, "%sbroken paths: %s" % (aliasinfo, ",".join(broken)))

    if target_numpaths == None:
        target_numpaths = 2 # default case: we need two paths
    elif type(target_numpaths) == tuple:
        warn, crit = target_numpaths
        warn_num  = (warn / 100.0) * numpaths
        crit_num = (crit / 100.0) * numpaths
        levels = " (Warning/ Critical at %d/ %d)" % (warn_num, crit_num)
        info = "%spaths active: %d" % (aliasinfo, numpaths)
        if numpaths <= crit_num:
            return 2, info + levels
        elif numpaths <= warn_num:
            return 1, info + levels
        else:
            return 0, info

    info = "%spaths expected: %d, paths active: %d" % (aliasinfo, target_numpaths, numpaths)

    if numpaths < target_numpaths:
        return 2, info
    elif numpaths > target_numpaths:
        return 1, info
    else:
        return 0, info

check_info["multipath"] = {
    'check_function':          check_multipath,
    'inventory_function':      inventory_multipath,
    'parse_function':          parse_multipath,
    'service_description':     'Multipath %s',
    'group':                   'multipath',
}


# /omd/sites/prod/share/check_mk/checks/local



def local_compute_state(perfdata):
    texts = []

    def float_ignore_uom(value):
        while value:
            if value[-1] not in "0123456789.-":
                value = value[:-1]
            else:
                return float(value)
        return 0.0


    def outof_levels(value, levels):
        if levels == None:
            return

        if ':' in levels:
            lower, upper = map(float, levels.split(':'))
        else:
            lower = None
            upper = float(levels)
        if value > upper:
            return " %s > %s" % (value, upper)
        elif lower != None and value < lower:
            return " %s < %s" % (value, lower)

    worst = 0
    for entry in perfdata:
        if len(entry) < 3:
            continue # No levels attached
        varname = entry[0]
        value = float_ignore_uom(entry[1])
        warn = entry[2]
        if len(entry) >= 4:
            crit = entry[3]
        else:
            crit = None

        text = outof_levels(value, crit)
        if text:
            worst = 2
            text = "%s%s(!!)" % (varname, text)
            texts.append(text)

        else:
            text = outof_levels(value, warn)
            if text:
                worst = max(worst, 1)
                text = "%s%s(!)" % (varname, text)
                texts.append(text)

            else:
                texts.append("%s is %s(.)" % (varname, value))

    return worst, texts


def inventory_local(info):
    inventory = []
    for line in info:
        if len(line) >= 4 or len(line) == 3 and line[0] == 'P':
            inventory.append( (line[1], None) )
        else:
            raise MKGeneralException("Invalid line in agent section <<<local>>>: %s" % " ".join(line))
    return inventory


def check_local(item, params, info):
    for line in info:
        if len(line) >= 2 and line[1] == item:
            if not (len(line) >= 4 or (len(line) == 3 and line[0] == 'P')):
                return 3, "Incomplete line in local check output: %s" % " ".join(line)

            statechar = line[0]
            perftxt = line[2]

            output = " ".join(line[3:])
            output = output.replace("\\n", "\n")

            perfdata = []
            if perftxt != "-":
                for entry in perftxt.split('|'):
                    try:
                        varname, valuetxt = entry.split('=')
                        values = valuetxt.split(';')
                        perfdata.append(tuple( [varname] + values ))
                    except ValueError:
                        return 3, "Invalid performance data %s in local check output %s" % \
                                  (perftxt, " ".join(line))
            if statechar == 'P':
                state, texts = local_compute_state(perfdata)
                if output:
                    texts = [output] + texts
                output = ", ".join(texts)
            else:
                try:
                    state = int(statechar)
                except:
                    return 3, "Invalid state %s in local check output %s: must be P, 0, 1, 2 or 3" % \
                             (statechar, " ".join(line))

                if state not in range(0, 4):
                    output += ", local check has sent invalid state %d" % state
                    state = 3
            return (state, output, perfdata)


check_info["local"] = {
    'check_function':          check_local,
    'inventory_function':      inventory_local,
    'service_description':     '%s',
    'has_perfdata':            True,
}


# /omd/sites/prod/share/check_mk/checks/if.include


if_inventory_porttypes = [ '6', '32', '62', '117', '127', '128', '129', '180', '181', '182', '205','229' ]
if_inventory_portstates = [ '1' ]
if_inventory_uses_description = False
if_inventory_uses_alias = False
if_inventory_pad_portnumbers = True
if_inventory_monitor_speed = True
if_inventory_monitor_state = True
inventory_if_rules = []

factory_settings["if_default_levels"] = {
    "errors" : (0.01, 0.1),
}


if_groups = []

if_default_error_levels = factory_settings["if_default_levels"]["errors"]
if_default_traffic_levels = None, None
if_default_average = None

if_disable_if64_hosts = [] # Binary host list for disabling if64 on some broken devices

def if64_disabled(hostname):
    return in_binary_hostlist(hostname, if_disable_if64_hosts)


def fix_if_64_highspeed(info):
    for line in info:
        if type(line[3]) in [ str, unicode ]: # not yet converted
            line[3] = saveint(line[3]) * 1000000


def cleanup_if_strings(s):
    if s and s != '':
        return "".join([ c for c in s if c not in nagios_illegal_chars+chr(0) ]).strip()
    else:
        return s

check_config_variables.append("nagios_illegal_chars")

def if_statename(st):
    names = {
        '1': 'up',
        '2': 'down',
        '3': 'testing',
        '4': 'unknown',
        '5': 'dormant',
        '6': 'not present',
        '7': 'lower layer down',
        '8': 'degraded',
        '9': 'admin down',
    }
    return names.get(st, st)

def if_extract_node(line, has_nodeinfo):
    if has_nodeinfo:
        return line[0], line[1:]
    else:
        return None, line

def if_item_matches(item, ifIndex, ifAlias, ifDescr):
    return item.lstrip("0") == ifIndex \
            or (item == "0" * len(item) and saveint(ifIndex) == 0) \
            or item == ifAlias \
            or item == ifDescr \
            or item == "%s %s" % (ifAlias, ifIndex) \
            or item == "%s %s" % (ifDescr, ifIndex)

def if_pad_with_zeroes(info, ifIndex, has_nodeinfo, pad_portnumbers):
    if has_nodeinfo:
        index = 1
    else:
        index = 0
    if pad_portnumbers:
        def get_index(line):
            if type(line[index]) == tuple:
                return line[index][1]
            else:
                return line[index]

        max_index = max([int(get_index(line)) for line in info])
        digits = len(str(max_index))
        return ("%0"+str(digits)+"d") % int(ifIndex)
    else:
        return ifIndex


def if_get_traffic_levels(params):
    new_traffic = []
    if 'traffic' in params and type(params['traffic']) != list:
        warn, crit = params['traffic']
        if warn == None:
            new_traffic.append(('both', ('upper', (None, (None, None)))))
        elif type(warn) == int:
            new_traffic.append(('both', ('upper', ('abs', (warn, crit)))))
        elif type(warn) == float:
            new_traffic.append(('both', ('upper', ('perc', (warn, crit)))))

    if 'traffic_minimum' in params:
        warn, crit = params['traffic_minimum']
        if type(warn) == int:
            new_traffic.append(('both', ('lower', ('abs', (warn, crit)))))
        elif type(warn) == float:
            new_traffic.append(('both', ('lower', ('perc', (warn, crit)))))
        del params['traffic_minimum']

    if new_traffic:
        traffic_levels = new_traffic
    else:
        traffic_levels = params.get('traffic', [])

    levels = {
        ('in',  'upper'): (None, (None, None)),
        ('out', 'upper'): (None, (None, None)),
        ('in',  'lower'): (None, (None, None)),
        ('out', 'lower'): (None, (None, None)),
    }
    for level in traffic_levels:
        traffic_dir = level[0]
        up_or_low   = level[1][0]
        level_type  = level[1][1][0]
        level_value = level[1][1][1]

        if traffic_dir == 'both':
            levels[('in', up_or_low)]  = (level_type, level_value)
            levels[('out', up_or_low)] = (level_type, level_value)
        else:
            levels[(traffic_dir, up_or_low)] = (level_type, level_value)

    return levels


def get_specific_traffic_levels(general_traffic_levels, unit, ref_speed, assumed_speed_in, assumed_speed_out):
    traffic_levels = {}
    for (traffic_dir, up_or_low), (level_type, levels) in general_traffic_levels.items():
        if type(levels) != tuple:
            traffic_levels[(traffic_dir, 'predictive')] = levels
            traffic_levels[(traffic_dir, up_or_low, 'warn')] = None
            traffic_levels[(traffic_dir, up_or_low, 'crit')] = None
            continue # don't convert predictive levels config
        else:
            warn, crit = levels

        for what, level_value in [('warn', warn), ('crit', crit)]:
            if unit == 'Bit' and level_type == 'abs':
                level_value = level_value / 8
            elif level_type == 'perc':
                if traffic_dir == 'in' and assumed_speed_in:
                    level_value = level_value / 100.0 * assumed_speed_in / 8
                elif traffic_dir == 'out' and assumed_speed_out:
                    level_value = level_value / 100.0 * assumed_speed_out / 8
                elif ref_speed:
                    level_value = level_value / 100.0 * ref_speed
                else:
                    level_value = None

            traffic_levels[(traffic_dir, up_or_low, what)] = level_value # bytes
    return traffic_levels

def inventory_if_common(info, has_nodeinfo = False):
    if has_nodeinfo:
        length = 21
    else:
        length = 20
    if len(info) == 0 or len(info[0]) != length:
        return []

    settings            = host_extra_conf_merged(g_hostname, inventory_if_rules)
    uses_description    = settings.get('use_desc', if_inventory_uses_description)
    uses_alias          = settings.get('use_alias', if_inventory_uses_alias)
    porttypes           = settings.get('porttypes', if_inventory_porttypes)[:]
    portstates          = settings.get('portstates', if_inventory_portstates)
    match_alias         = settings.get('match_alias')
    match_desc          = settings.get('match_desc')
    pad_portnumbers     = settings.get('pad_portnumbers', if_inventory_pad_portnumbers)

    def port_match(name, what):
        if what == None:
            return True
        for r in what:
            if regex(r).match(name):
                return True
        return False

    porttypes.append("")

    pre_inventory        = []
    pre_inventory_groups = []
    group_patterns = {}

    for line in host_extra_conf(g_hostname, if_groups):
        for entry in line:
            group_patterns[entry["name"]] = entry

    seen_items  = set([])
    duplicate   = set([])
    have_groups = {}

    for line in info:
        node, line = if_extract_node(line, has_nodeinfo)
        ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus, ifInOctets, \
            inucast, inmcast, inbcast, ifInDiscards, ifInErrors, ifOutOctets, \
            outucast, outmcast, outbcast, ifOutDiscards, ifOutErrors, \
            ifOutQLen, ifAlias, ifPhysAddress = line

        if type(ifOperStatus) == tuple:
            ifOperStatus = ifOperStatus[0]

        ifGroup = None
        if type(ifIndex) == tuple:
            ifGroup, ifIndex = ifIndex

        ifDescr = cleanup_if_strings(ifDescr)
        ifAlias = cleanup_if_strings(ifAlias)

        if ifIndex == '':
            continue

        ifSpeed = saveint(ifSpeed)
        if ifSpeed > 9000000 * 100 * 1000:
            ifSpeed /= 1000000

        if uses_description and ifDescr:
            item = ifDescr
        elif uses_alias and ifAlias:
            item = ifAlias
        else:
            item = if_pad_with_zeroes(info, ifIndex, has_nodeinfo, pad_portnumbers)

        is_only_in_group = False
        for group_name, pattern in group_patterns.items():
            match_item = "include_items" not in pattern or (tryint(item) in map(tryint, pattern["include_items"]))
            match_type = "iftype" not in pattern        or (pattern["iftype"] == saveint(ifType))
            if match_item and match_type:
                have_groups.setdefault(group_name, {"interfaces": []})
                for what in [ "iftype", "include_items" ]:
                    if pattern.get(what):
                        have_groups[group_name][what] = pattern.get(what)

                have_groups[group_name]["interfaces"].append((saveint(ifSpeed), ifOperStatus, ifType))
                if pattern.get("single"):
                    is_only_in_group = True

        if ifGroup:
            have_groups.setdefault(ifGroup, {"interfaces": [],
                                             "iftype": ifType,
                                             "include_items": []})
            have_groups[ifGroup]["interfaces"].append((saveint(ifSpeed), ifOperStatus, ifType))
            is_only_in_group = True

        if not is_only_in_group:
            if item in seen_items: # duplicate
                duplicate.add(item)
            seen_items.add(item)

            if ifType in porttypes and ifOperStatus in portstates and \
                port_match(ifAlias, match_alias) and port_match(ifDescr, match_desc):
                params = {}
                if if_inventory_monitor_state:
                    params["state"] = [ifOperStatus]

                if ifSpeed != "" and if_inventory_monitor_speed:
                    params["speed"] = int(ifSpeed)
                pre_inventory.append( (item, "%r" % params, int(ifIndex)) )

    for group_name, values in have_groups.items():
        total_speed = sum([pair[0] for pair in values["interfaces"]])
        one_up = "1" in [pair[1] for pair in values["interfaces"]]
        group_operStatus = one_up and "1" or "2"

        if group_operStatus in portstates:
            params = { "aggregate": True }
            for what in [ "iftype", "include_items" ]:
                if what in values:
                    params[what] = values[what]

            if uses_description:
                params["aggr_member_item"] = "description"
            elif uses_alias:
                params["aggr_member_item"] = "alias"
            else:
                params["aggr_member_item"] = "index"

            if if_inventory_monitor_state:
                params["state"] = [group_operStatus]

            if ifSpeed != "" and if_inventory_monitor_speed:
                params["speed"] = total_speed

            pre_inventory.append((group_name, "%r" % params, 1))

    inventory = []
    for item, params, index in pre_inventory:
        if item in duplicate:
            new_item = "%s %d" % (item, index)
        else:
            new_item = item
        inventory.append((new_item, params))

    return inventory

def check_if_common(item, params, info, has_nodeinfo = False, group_name = "Group"):
    if params.get("aggregate"):
        group_members = []
        matching_interfaces = []

        for element in info:
            node, line = if_extract_node(element, has_nodeinfo)
            ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus, ifInOctets, \
                inucast, inmcast, inbcast, ifInDiscards, ifInErrors, ifOutOctets, \
                outucast, outmcast, outbcast, ifOutDiscards, ifOutErrors, \
                ifOutQLen, ifAlias, ifPhysAddress = line

            ifGroup = None
            if type(ifIndex) == tuple:
                ifGroup, ifIndex = ifIndex

            service_name_type = params.get("aggr_member_item")
            if service_name_type == "description":
                if_member_item = ifDescr
            elif service_name_type == "alias":
                if_member_item = ifAlias
            else: # index
                pad_portnumbers = item[0] == '0'
                if_member_item = if_pad_with_zeroes(info, ifIndex, has_nodeinfo, pad_portnumbers)

            if ifGroup and ifGroup == item:
                matching_interfaces.append((if_member_item, element))
            else:
                add_interface = True # This approach is easier to comprehend..
                if params.get("include_items") != None and tryint(if_member_item) not in map(tryint, params["include_items"]):
                    add_interface = False
                elif params.get("iftype") != None and saveint(ifType) != params["iftype"]:
                    add_interface = False
                if add_interface:
                    matching_interfaces.append((if_member_item, element))

        wrapped = False
        this_time = time.time()

        group_info = {
            "ifSpeed"      : 0, "ifInOctets"    : 0, "inucast"     : 0, "inmcast"   : 0, "inbcast" : 0,
            "ifInDiscards" : 0, "ifInErrors"    : 0, "ifOutOctets" : 0, "outucast"  : 0, "outmcast" : 0,
            "outbcast"     : 0, "ifOutDiscards" : 0, "ifOutErrors" : 0, "ifOutQLen" : 0
        }

        for (if_member_item, element) in matching_interfaces:
            node, line = if_extract_node(element, has_nodeinfo)
            ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus, ifInOctets, \
                inucast, inmcast, inbcast, ifInDiscards, ifInErrors, ifOutOctets, \
                outucast, outmcast, outbcast, ifOutDiscards, ifOutErrors, \
                ifOutQLen, ifAlias, ifPhysAddress = line

            if type(ifOperStatus) == tuple:
                ifOperStatus, ifOperStatusName = ifOperStatus
            else:
                ifOperStatusName = if_statename(ifOperStatus)

            if has_nodeinfo and node:
                return 3, "Interface grouping is not supported for clusters."

            ifGroup = None
            if type(ifIndex) == tuple:
                ifGroup, ifIndex = ifIndex

            group_members.append({"name": if_member_item, "state": ifOperStatus, "state_name" : ifOperStatusName})
            perfdata = []

            for name, counter in [
                ( "in",        ifInOctets),
                ( "inucast",   inucast),
                ( "inmcast",   inmcast),
                ( "inbcast",   inbcast),
                ( "indisc",    ifInDiscards),
                ( "inerr",     ifInErrors),

                ( "out",       ifOutOctets),
                ( "outucast",  outucast),
                ( "outmcast",  outmcast),
                ( "outbcast",  outbcast),
                ( "outdisc",   ifOutDiscards),
                ( "outerr",    ifOutErrors) ]:
                try:
                    get_rate("if.%s.%s.%s" % (name, item, if_member_item), this_time, saveint(counter), onwrap=RAISE)
                except MKCounterWrapped:
                    wrapped = True

            group_info["ifSpeed"]       += ifOperStatus == "1" and saveint(ifSpeed) or 0
            group_info["ifInOctets"]    += saveint(ifInOctets)
            group_info["inucast"]       += saveint(inucast)
            group_info["inmcast"]       += saveint(inmcast)
            group_info["inbcast"]       += saveint(inbcast)
            group_info["ifInDiscards"]  += saveint(ifInDiscards)
            group_info["ifInErrors"]    += saveint(ifInErrors)
            group_info["ifOutOctets"]   += saveint(ifOutOctets)
            group_info["outucast"]      += saveint(outucast)
            group_info["outmcast"]      += saveint(outmcast)
            group_info["outbcast"]      += saveint(outbcast)
            group_info["ifOutDiscards"] += saveint(ifOutDiscards)
            group_info["ifOutErrors"]   += saveint(ifOutErrors)
            group_info["ifOutQLen"]     += saveint(ifOutQLen)

            group_info["ifType"] = ifType # This is the fallback ifType if none is set in the parameters

        num_up = 0
        for (if_member_item, element) in matching_interfaces:
            node, line = if_extract_node(element, has_nodeinfo)
            ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus, ifInOctets, \
                inucast, inmcast, inbcast, ifInDiscards, ifInErrors, ifOutOctets, \
                outucast, outmcast, outbcast, ifOutDiscards, ifOutErrors, \
                ifOutQLen, ifAlias, ifPhysAddress = line

            if ifOperStatus == '1' or (
                type(ifOperStatus) == tuple and ifOperStatus[0] == '1'):
                num_up += 1

        if num_up == len(matching_interfaces):
            group_operStatus = "1" # up
        elif num_up > 0:
            group_operStatus = "8" # degraded
        else:
            group_operStatus = "2" # down

        alias_info = []
        if params.get("iftype"):
            alias_info.append("iftype %s" % params["iftype"])
        if params.get("include_items"):
            alias_info.append("%d grouped interfaces" % len(matching_interfaces))

        if has_nodeinfo:
            group_entry = [None]
        else:
            group_entry = []

        if params.get("ifType"):
            group_info["ifType"] = params["ifType"]

        group_entry += [
                    "ifgroup%s" % item,         # ifIndex
                    item,                       # ifDescr
                    group_info["ifType"],       # ifType
                    group_info["ifSpeed"],      # ifSpeed
                    group_operStatus,           # ifOperStatus
                    group_info["ifInOctets"],   # ifInOctets
                    group_info["inucast"],      # inucast
                    group_info["inmcast"],      # inmcast
                    group_info["inbcast"],      # inbcast
                    group_info["ifInDiscards"], # ifInDiscards
                    group_info["ifInErrors"],   # ifInErrors

                    group_info["ifOutOctets"],  # ifOutOctets
                    group_info["outucast"],     # outucast
                    group_info["outmcast"],     # outmcast
                    group_info["outbcast"],     # outbcast
                    group_info["ifOutDiscards"],# ifOutDiscards
                    group_info["ifOutErrors"],  # ifOutErrors
                    group_info["ifOutQLen"],    # ifOutQLen
                    " and ".join(alias_info),
                    "",                         # ifPhysAddress
        ]

        return check_if_common_single(item, params, [group_entry], wrapped,
                     has_nodeinfo = has_nodeinfo, group_members = group_members, group_name = group_name)

    return check_if_common_single(item, params, info, has_nodeinfo=has_nodeinfo, group_name = group_name)


def check_if_common_single(item, params, info, force_counter_wrap = False,
                           has_nodeinfo = False, group_members = None, group_name = "Group"):
    targetspeed        = params.get("speed")
    assumed_speed_in   = params.get("assumed_speed_in")
    assumed_speed_out  = params.get("assumed_speed_out")
    targetstate        = params.get("state")
    average            = params.get("average")
    unit               = params.get("unit") in ["Bit", "bit"] and "Bit" or "B"
    unit_multiplier    = unit == "Bit" and 8.0 or 1.0
    cluster_items      = {}

    if params["errors"]:
        err_warn, err_crit = params["errors"]
    else:
        err_warn, err_crit = None, None

    if "nucasts" in params:
        nucast_warn, nucast_crit = params["nucasts"]
    else:
        nucast_warn, nucast_crit = None, None

    general_traffic_levels = if_get_traffic_levels(params)

    for line in info:
        node, line = if_extract_node(line, has_nodeinfo)
        ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus, ifInOctets,  \
            inucast, inmcast, inbcast, ifInDiscards, ifInErrors, ifOutOctets, \
            outucast, outmcast, outbcast, ifOutDiscards, ifOutErrors, \
            ifOutQLen, ifAlias, ifPhysAddress = line

        if type(ifOperStatus) == tuple:
            ifOperStatus, ifOperStatusName = ifOperStatus
        else:
            ifOperStatusName = if_statename(ifOperStatus)

        ifGroup = None
        if type(ifIndex) == tuple:
            ifGroup, ifIndex = ifIndex

        ifDescr = cleanup_if_strings(ifDescr)
        ifAlias = cleanup_if_strings(ifAlias)

        if if_item_matches(item, ifIndex, ifAlias, ifDescr):
            if group_members:
                infotext = group_name + " Status "
            else:
                if "infotext_format" in params:
                    bracket_info = ""
                    if   params["infotext_format"] == "alias":
                        bracket_info = ifAlias
                    elif params["infotext_format"] == "description":
                        bracket_info = ifDescr
                    elif params["infotext_format"] == "alias_and_description":
                        bracket_info = []
                        ifAlias and bracket_info.append(ifAlias)
                        ifDescr and bracket_info.append(ifDescr)
                        bracket_info = ", ".join(bracket_info)
                    elif params["infotext_format"] == "alias_or_description":
                        bracket_info = ifAlias and ifAlias or ifDescr
                    elif params["infotext_format"] == "desription_or_alias":
                        bracket_info = ifDescr and ifDescr or ifAlias

                    if bracket_info:
                        infotext = "[%s]" % bracket_info
                    else:
                        infotext = ""
                else:
                    if item.lstrip("0") == ifIndex \
                        and (item == ifAlias or ifAlias == '') \
                        and (item == ifDescr or ifDescr == ''): # description trivial
                        infotext = ""
                    elif item == "%s %s" % (ifAlias, ifIndex) and ifDescr != '': # non-unique Alias
                        infotext = "[%s/%s]" % (ifAlias, ifDescr)
                    elif item != ifAlias and ifAlias != '': # alias useful
                        infotext = "[%s] " % ifAlias
                    elif item != ifDescr and ifDescr != '': # description useful
                        infotext = "[%s] " % ifDescr
                    else:
                        infotext = "[%s] " % ifIndex

                if node != None:
                    infotext = "%son %s: " % ( infotext, node )

            state = 0

            if targetstate and  \
                (ifOperStatus != targetstate
                and not (type(targetstate) in [ list, tuple ] and ifOperStatus in targetstate)):
                state = 2
                infotext += "(%s)(!!) " % ifOperStatusName
            else:
                infotext += "(%s) " % ifOperStatusName

            if group_members:
                infotext = infotext[:-1] # remove last space
                extra_info = ", Members: "
                member_info = []
                for member in group_members:
                    member_info.append("%s (%s)" % (member["name"], member["state_name"]))
                infotext += extra_info + "[%s] " % ", ".join(member_info)

            speed = saveint(ifSpeed)
            if speed:
                if speed > 9 * 1000 * 1000 * 1000 * 1000:
                    speed /= (1000 * 1000)
                ref_speed = speed / 8.0
            elif targetspeed:
                ref_speed = targetspeed / 8.0
            else:
                ref_speed = None


	    if ifPhysAddress:
                if type(ifPhysAddress) != list:
                    mac_bytes = map(ord, ifPhysAddress)
                else:
                    mac_bytes = ifPhysAddress
                mac = ":".join(["%02s" % hex(m)[2:] for m in mac_bytes]).replace(' ', '0')
                infotext += 'MAC: %s, ' % mac

            if speed:
                infotext += get_nic_speed_human_readable(speed)
                if not targetspeed is None and speed != targetspeed:
                    infotext += " (wrong speed, expected: %s)(!)" % get_nic_speed_human_readable(targetspeed)
                    state = max(state, 1)
            elif targetspeed:
                infotext += "assuming %s" % get_nic_speed_human_readable(targetspeed)
            else:
                infotext += "speed unknown"

            traffic_levels = get_specific_traffic_levels(general_traffic_levels, unit, ref_speed, assumed_speed_in, assumed_speed_out)

            speed_b_in  = assumed_speed_in  and assumed_speed_in / 8  or ref_speed
            speed_b_out = assumed_speed_out and assumed_speed_out / 8 or ref_speed


            if str(ifOperStatus) == "2":
                return state, infotext

            this_time = time.time()
            rates = []
            wrapped = False
            perfdata = []
            for name, counter, warn, crit, mmin, mmax in [
                ( "in",        ifInOctets, traffic_levels[('in', 'upper', 'warn')], traffic_levels[('in', 'upper', 'crit')], 0, speed_b_in),
                ( "inucast",   inucast, None, None, None, None),
                ( "innucast",  saveint(inmcast) + saveint(inbcast), nucast_warn, nucast_crit, None, None),
                ( "indisc",    ifInDiscards, None, None, None, None),
                ( "inerr",     ifInErrors, err_warn, err_crit, None, None),

                ( "out",       ifOutOctets, traffic_levels[('out', 'upper', 'warn')], traffic_levels[('out', 'upper', 'crit')], 0, speed_b_out),
                ( "outucast",  outucast, None, None, None, None),
                ( "outnucast", saveint(outmcast) + saveint(outbcast), nucast_warn, nucast_crit, None, None),
                ( "outdisc",   ifOutDiscards, None, None, None, None),
                ( "outerr",    ifOutErrors, err_warn, err_crit, None, None) ]:

                try:
                    if node == None:
                        rate = get_rate("if.%s.%s" % (name, item), this_time, saveint(counter), onwrap=RAISE)
                        if force_counter_wrap:
                            raise MKCounterWrapped("Forced counter wrap")
                    else: # clustered check needs one counter per variable, item AND NODE
                        rate = get_rate("if.%s.%s.%s" % (node, name, item), this_time, saveint(counter), onwrap=RAISE)
                        if force_counter_wrap:
                            raise MKCounterWrapped("Forced counter wrap")
                    rates.append(rate)
                    perfdata.append( (name, rate, warn, crit, mmin, mmax) )
                except MKCounterWrapped:
                    wrapped = True

            if wrapped:
                if any(traffic_levels.values()):
                    raise MKCounterWrapped("Counter wrap, skipping checks this time")
                perfdata = []
            else:
                perfdata.append(("outqlen", saveint(ifOutQLen),"","", unit == "Bit" and "0.0" or "0"))
                def format_value(value):
                    if unit == "Bit":
                        return get_nic_speed_human_readable(value*8)
                    else:
                        return "%s/s" % get_bytes_human_readable(value)

                for what, errorrate, urate, nurate, traffic, speed in \
                   [ ("in",  rates[4], rates[1], rates[2], rates[0], speed_b_in),
                     ("out", rates[9], rates[6], rates[7], rates[5], speed_b_out) ]:

                    infotext += ", %s: %s" % (what, format_value(traffic))

                    if (what, 'predictive') in traffic_levels:
                        params = traffic_levels[(what, 'predictive')]
                        bw_warn, bw_crit = None, None
                    else:
                        bw_warn     = traffic_levels[(what, 'upper', 'warn')]
                        bw_crit     = traffic_levels[(what, 'upper', 'crit')]
                        bw_warn_min = traffic_levels[(what, 'lower', 'warn')]
                        bw_crit_min = traffic_levels[(what, 'lower', 'crit')]
                        params = (bw_warn, bw_crit, bw_warn_min, bw_crit_min)

                    if speed:
                        perc_used = 100.0 * traffic / speed

                        assumed_info = ""
                        if assumed_speed_in or assumed_speed_out:
                            assumed_info = "/" + format_value(speed)
                        infotext += "(%.1f%%%s)" % (perc_used, assumed_info)

                    if average:
                        traffic_avg = get_average("if.%s.%s.avg" % (what, item), this_time, traffic, average)
                        infotext += ", %dmin avg: %s" % (average, format_value(traffic_avg))
                        dsname = "%s_avg_%d" % (what, average)
                        perfdata.append((dsname, traffic_avg, bw_warn, bw_crit, 0, speed))
                        traffic = traffic_avg # apply levels to average traffic
                    else:
                        dsname = what

                    result = check_levels(traffic, dsname, params, statemarkers=True)
                    state = max(state, result[0])
                    infotext += result[1]
                    perfdata += result[2]

                    pacrate = urate + nurate + errorrate
                    if pacrate > 0.0: # any packets transmitted?
                        errperc = 100.0 * errorrate / pacrate
                        if errperc > 0:
                            infotext += ", %s-errors: %.2f%%" % (what, errperc)
                            if type(err_crit) == float: # percentual levels
                                if errperc >= err_crit:
                                    state = 2
                                    infotext += "(!!) >= %s%%" % str(err_crit)
                                elif errperc >= err_warn:
                                    state = max(state, 1)
                                    infotext += "(!) >= %s%%" % str(err_warn)
                            elif type(err_crit) == int: # absolute levels
                                if errorrate >= err_crit:
                                    state = 2
                                    infotext += ", %s-error packets: %d (!!) >= %s" % (what, errorrate, err_crit)
                                elif errorrate >= err_warn:
                                    state = max(state, 1)
                                    infotext += ", %s-errors packets: %d (!!) >= %s" % (what, errorrate, err_warn)


                    if nucast_crit or nucast_warn:
                        infotext += ", %s non-unicast packets %.2f/s" % (what, nurate)

                        if nucast_crit and nurate >= nucast_crit:
                            state = 2
                            infotext += "(!!) >= " + str(nucast_crit)
                        elif nucast_warn and nurate >= nucast_warn:
                            state = max(state,1)
                            infotext += "(!) >= " + str(nucast_warn)

            if node:
                cluster_items[node] = ( state, infotext, perfdata )
            else:
                return (state, infotext, perfdata)

    if cluster_items:
        maxval = 0
        choosen_node = None
        for node, result in cluster_items.items():
            state, infotext, perfdata = result
            for entry in perfdata:
                name, value = entry[:2]
                if name == "out":
                    maxval = max(maxval, value)
                    if maxval == value:
                        choosen_node = node
        if not choosen_node:
            choosen_node = node
        return cluster_items[choosen_node]

    return (3, "no such interface")






# /omd/sites/prod/share/check_mk/checks/lnx_if




check_includes['lnx_if'] = [ "if.include" ]

linux_nic_check = "lnx_if"

def if_lnx_extract_nic_info(info):
    nic_info = {}
    current_nic = None
    index = 0
    lines = iter(info)
    iplink_stats = {}
    while True:
        try:
            line = lines.next()
        except StopIteration:
            break

        if line[0].startswith("[start_iplink]"):
            iplink_stats = {}
            try:
                while True:
                    line = lines.next()
                    if line[0].startswith("[end_iplink]"):
                        line = lines.next()
                        break
                    if line[0].startswith("alias"):
                        continue
                    status_info = line
                    link_info   = lines.next() # currently unused
                    try:
                        nic_name = status_info[1][:-1]
                        iplink_stats.setdefault(nic_name, { "extra_info": status_info[2][1:-1].split(",") })
                        iplink_stats[nic_name].update(dict(zip(status_info[3::2], status_info[4::2])))
                    except: # In case of parse errors we simply ignore these lines
                        pass
            except StopIteration:
                break

        if line[0].startswith('['):
            current_nic = line[0][1:-1]
            index += 1
            nic_info[current_nic]['index'] = index
            iplink_stats = {}
        elif len(line) == 2 and len(line[1].split()) >= 16:
            nic = line[0]
            nic_info[nic] = { "counters": map(int, line[1].split()) }
            if nic in iplink_stats:
                nic_info[nic]['iplink_stats'] = iplink_stats[nic]
        elif current_nic:
            nic_info[current_nic][line[0].strip()] = ":".join(line[1:]).strip()

    return nic_info


def if_lnx_convert_to_if64(info):
    nic_info = if_lnx_extract_nic_info(info)

    if_table = []
    index = 0
    for nic, attr in nic_info.items():
        counters = attr.get("counters", [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])
        index += 1
        ifIndex = attr.get("index",index)
        ifDescr = nic
        ifAlias = nic

        if nic == "lo":
            ifType = 24
        else:
            ifType = 6

        speed_text = attr.get("Speed")
        if speed_text == None:
            ifSpeed = ''
        else:
            if speed_text == '65535Mb/s': # unknown
                ifSpeed = ''
            elif speed_text.endswith("Kb/s"):
                ifSpeed = int(speed_text[:-4]) * 1000
            elif speed_text.endswith("Mb/s"):
                ifSpeed = int(speed_text[:-4]) * 1000000
            elif speed_text.endswith("Gb/s"):
                ifSpeed = int(speed_text[:-4]) * 1000000000
            else:
                ifSpeed = ''

        ifInOctets = counters[0]
        inucast = counters[1] + counters[7]
        inmcast = counters[7]
        inbcast = 0
        ifInDiscards = counters[3]
        ifInErrors = counters[2]
        ifOutOctets = counters[8]
        outucast = counters[9]
        outmcast = 0
        outbcast = 0
        ifOutDiscards = counters[11]
        ifOutErrors = counters[10]
        ifOutQLen = counters[12]

        ld = attr.get("Link detected")
        if ld == "yes":
            ifOperStatus = 1
        elif ld == "no":
            ifOperStatus = 2
        else:
            iplink_stats = attr.get("iplink_stats")
            if iplink_stats:
                if "UP" in iplink_stats.get("extra_info", []) or iplink_stats.get("state") == "UP":
                    ifOperStatus = 1
                elif iplink_stats.get("state") == "DOWN":
                    ifOperStatus = 2
                else:
                    ifOperStatus = 4
            else:
                if ifInOctets > 0:
                    ifOperStatus = 1 # assume up
                else:
                    ifOperStatus = 4 # unknown (NIC has never been used)

        if attr.get("Address"):
            ifPhysAddress = "".join([chr(int(x, 16)) for x in attr.get("Address", "").split(":")])
        else:
            ifPhysAddress = ''

        if_table.append(map(str, [
          ifIndex, ifDescr, ifType, ifSpeed, ifOperStatus,
          ifInOctets, inucast, inmcast, inbcast, ifInDiscards,
          ifInErrors, ifOutOctets, outucast, outmcast, outbcast,
          ifOutDiscards, ifOutErrors, ifOutQLen, ifAlias, ifPhysAddress ]))

    return if_table

def inventory_lnx_if(info):
    if linux_nic_check == "legacy":
        return []
    return inventory_if_common(if_lnx_convert_to_if64(info))

def check_lnx_if(item, params, info):
    return check_if_common(item, params, if_lnx_convert_to_if64(info))


check_info["lnx_if"] = {
    'check_function':          check_lnx_if,
    'inventory_function':      inventory_lnx_if,
    'service_description':     'Interface %s',
    'has_perfdata':            True,
    'group':                   'if',
    'default_levels_variable': 'if_default_levels',
}


# /omd/sites/prod/share/check_mk/checks/mem.include

memused_default_levels = (150.0, 200.0)

factory_settings["memory_default_levels"] = {
    "levels" : memused_default_levels,
}

def parse_proc_meminfo_bytes(info):
    meminfo = {}
    for line in info:
        value = int(line[1])
        if len(line) > 2 and line[2] == 'kB':
            value *= 1024
        meminfo[line[0][:-1]] = value
    return meminfo

def check_memory(params, meminfo):
    swapused = meminfo['SwapTotal'] - meminfo['SwapFree']
    memused  = meminfo['MemTotal']  - meminfo['MemFree']

    caches   = meminfo.get('Buffers', 0) + meminfo.get('Cached', 0)

    pagetables = meminfo.get('PageTables', 0)
    pagetables_mb = pagetables / 1024.0

    totalused_kb = (swapused + memused - caches + pagetables)
    totalused_mb = totalused_kb / 1024.0
    totalmem_kb = meminfo['MemTotal']
    totalmem_mb = totalmem_kb / 1024.0
    totalused_perc = 100 * (float(totalused_kb) / float(totalmem_kb))
    totalvirt_mb = (meminfo['SwapTotal'] + meminfo['MemTotal']) / 1024.0

    if type(params) == tuple:
        params = { "levels" : params }
    warn, crit = params["levels"]

    if pagetables > 0:
        pgtext = " + %.2f Pagetables" % (pagetables_mb / 1024.0)
    else:
        pgtext = ""
    infotext = "%.2f GB used (%.2f RAM + %.2f SWAP%s, this is %.1f%% of %.2f RAM (%.2f total SWAP)" % \
               (totalused_mb / 1024.0, (memused-caches) / 1024.0 / 1024, swapused / 1024.0 / 1024,
               pgtext, totalused_perc, totalmem_mb / 1024.0, meminfo["SwapTotal"] / 1024.0 / 1024)

    average_min = params.get("average")
    if average_min:
        totalused_mb_avg = get_average("mem.used.total", time.time(),
                                                totalused_mb, average_min, initialize_zero = False)
        totalused_perc_avg = totalused_mb_avg / totalmem_mb * 100
        infotext += ", %d min average %.1f%%" % (average_min, totalused_perc_avg)
        comp_mb = totalused_mb_avg
    else:
        comp_mb = totalused_mb
        infotext += ")"


    if type(warn) == float:
        warn_mb = int(warn/100.0 * totalmem_mb)
        crit_mb = int(crit/100.0 * totalmem_mb)
        leveltext = lambda x: "%.1f%%" % x
    else:
        warn_mb = warn
        crit_mb = crit
        leveltext = lambda x: "%.2f GB" % (x / 1024.0)

    perfdata = [
        ('ramused',  str( (memused - caches) / 1024) + 'MB', '', '', 0, totalmem_mb),
        ('swapused', str(swapused / 1024) + 'MB', '', '', 0, meminfo['SwapTotal']/1024),
        ('memused',  str(totalused_mb) + 'MB', warn_mb, crit_mb, 0, totalvirt_mb),
    ]

    if average_min:
        perfdata.append(('memusedavg', str(totalused_mb_avg)+'MB'))

    state = 0
    if warn_mb > 0: # positive levels - used memory
        if comp_mb >= crit_mb:
            state = 2
            infotext += ", critical at %s used" % leveltext(crit)
        elif comp_mb >= warn_mb:
            state = 1
            infotext += ", warning at %s used" % leveltext(warn)
    else:           # negative levels - free memory
        freemem_mb = totalvirt_mb - comp_mb
        if freemem_mb <= -crit_mb:
            state = 2
            infotext += ", critical at %s free" % leveltext(-crit)
        elif freemem_mb <= -warn_mb:
            state = 1
            infotext += ", warning at %s free" % leveltext(-warn)


    mapped = meminfo.get('Mapped')
    if mapped:
        mapped_mb       = int(mapped) / 1024
        committed_as_mb = int(meminfo.get('Committed_AS', 0)) / 1024
        shared_mb       = int(meminfo.get('Shmem', 0)) / 1024

        perfdata += [
            ('mapped',       str(mapped_mb)       + 'MB'),
            ('committed_as', str(committed_as_mb) + 'MB'),
            ('pagetables',   str(pagetables_mb)   + 'MB'),
            ('shared',       str(shared_mb)       + 'MB'),
        ]
        infotext += ", %.1f mapped, %.1f committed, %.1f shared" % \
                    (mapped_mb / 1024.0, committed_as_mb / 1024.0, shared_mb / 1024.0)

    return state, infotext, perfdata


# /omd/sites/prod/share/check_mk/checks/mem







factory_settings["mem_linux_default_levels"] = {
    "levels_virtual":       ("perc_used", ( 80.0,  90.0)),
    "levels_total":         ("perc_used", (120.0, 150.0)),
    "levels_shm":           ("perc_used", ( 20.0,  30.0)),
    "levels_pagetables":    ("perc_used", (  8.0,  16.0)),
    "levels_committed":     ("perc_used", (100.0, 150.0)),
    "levels_commitlimit":   ("perc_free", ( 20.0,  10.0)),
    "levels_vmalloc":       ("abs_free",  (50*1024*1024, 30*1024*1024)),
}

def is_linux_meminfo(meminfo):
    return "PageTables" in meminfo and "Writeback" in meminfo and "Committed_AS" in meminfo

def inventory_mem_linux(info):
    meminfo = parse_proc_meminfo_bytes(info)
    if is_linux_meminfo(meminfo):
        return [ (None, {}) ]


def check_mem_levels(title, used, total, levels, of_what=None, of_value=None, show_percentage=False, show_free=False):
    if of_value == None:
        of_value = total # Reference for percentage levels
    state = 0
    if of_what:
        if show_free:
            value = total - used
        else:
            value = used
        infotext = "%s: %s" % (title, get_bytes_human_readable(value))
    else:
        infotext = "%s used: %s of %s" % (
             title, get_bytes_human_readable(used), get_bytes_human_readable(total))

    perc_shown = False
    if levels and levels != "ignore":
        how = levels[0]
        if how == "predictive":
            return 3, "Predictive levels for memory check not yet implemented"

        warn, crit = levels[1]
        if how.startswith("perc_"):
            perc_used = 100.0 * float(used) / of_value
            perc_free = 100 - perc_used
            if how == "perc_used":
                if of_what:
                    t = " of " + of_what
                else:
                    t = ""
                levels_text = " (%.1f%%%s, " % (perc_used, t)
                if perc_used >= crit:
                    state = 2
                elif perc_used >= warn:
                    state = 1

            elif how == "perc_free":
                if of_what:
                    t = "of " + of_what
                else:
                    t = "free"
                levels_text = " (%.1f%% %s, " % (perc_free, t)
                if perc_free < crit:
                    state = 2
                elif perc_free < warn:
                    state = 1

            if state:
                perc_shown = True
                infotext += levels_text + "warn/crit at %.1f%%/%.1f%%)" % (warn, crit)

        else:
            if how == "abs_used":
                if used >= crit:
                    state = 2
                elif used >= warn:
                    state = 1
            else:
                free = total - used
                if free < crit:
                    state = 2
                elif free < warn:
                    state = 1

            if state:
                infotext += " (warn/crit at %s/%s)" % (get_bytes_human_readable(warn), get_bytes_human_readable(crit))

    if not perc_shown and show_percentage:
        infotext += " (%.1f%%)" % (100.0 * float(used) / of_value)
    return state, infotext

def check_mem_linux(_no_item, params, info):
    meminfo = parse_proc_meminfo_bytes(info)

    if "SReclaimable" not in meminfo:
        meminfo["SReclaimable"] = 0
        meminfo["SUnreclaim"] = meminfo["Slab"]

    meminfo["Caches"] = meminfo["Cached"] + meminfo["Buffers"] \
                      + meminfo["SwapCached"] + meminfo["SReclaimable"]

    meminfo["MemUsed"] = meminfo["MemTotal"] - meminfo["MemFree"] - meminfo["Caches"]
    yield check_mem_levels("RAM", meminfo["MemUsed"], meminfo["MemTotal"],
              params.get("levels_ram"), show_percentage=not meminfo["SwapTotal"])

    meminfo["SwapUsed"] = meminfo["SwapTotal"] - meminfo["SwapFree"]
    if meminfo["SwapTotal"]:
        yield check_mem_levels("Swap", meminfo["SwapUsed"], meminfo["SwapTotal"],
                  params.get("levels_swap"))

    meminfo["TotalTotal"] = meminfo["MemTotal"] + meminfo["SwapTotal"]
    meminfo["TotalUsed"] = meminfo["MemUsed"] + meminfo["SwapUsed"]
    r = check_mem_levels("Total virtual memory", meminfo["TotalUsed"], meminfo["TotalTotal"],
              params.get("levels_virtual"), show_percentage=True)
    if r[0] or meminfo["SwapTotal"]:
        yield r # only display if there is swap or status is non-OK

    r = check_mem_levels("RAM + Swap", meminfo["TotalUsed"], meminfo["TotalTotal"],
              params.get("levels_total"), of_what = "RAM", of_value = meminfo["MemTotal"])
    if r[0]:
        yield r # only display if non-OK

    if "Shmem" in meminfo:
        r = check_mem_levels("Shared memory", meminfo["Shmem"], meminfo["MemTotal"],
                params.get("levels_shm"), of_what = "RAM")
        if r[0]:
            yield r # only display if non-OK

    r = check_mem_levels("Page tables", meminfo["PageTables"], meminfo["MemTotal"],
            params.get("levels_pagetables"), of_what = "RAM")
    if r[0]:
        yield r # only display if non-OK

    meminfo["Pending"] = \
         meminfo["Dirty"] \
       + meminfo.get("Writeback", 0) \
       + meminfo.get("NFS_Unstable", 0) \
       + meminfo.get("Bounce", 0) \
       + meminfo.get("WritebackTmp", 0)

    r = check_mem_levels("Disk Writeback", meminfo["Pending"], meminfo["MemTotal"],
            params.get("levels_writeback"), of_what = "RAM")
    if r[0]:
        yield r # only display if non-OK

    r = check_mem_levels("Committed", meminfo["Committed_AS"], meminfo["TotalTotal"],
            params.get("levels_committed"), of_what = "RAM + Swap")
    if r[0]:
        yield r # only display if non-OK

    if "CommitLimit" in meminfo:
        r = check_mem_levels("Commit Limit", meminfo["TotalTotal"] - meminfo["CommitLimit"],
                meminfo["TotalTotal"], params.get("levels_commitlimit"), of_what = "RAM + Swap")
        if r[0]:
            yield r # only display if non-OK

    if not (meminfo["VmallocUsed"] == 0 and meminfo["VmallocChunk"] == 0):
        r = check_mem_levels("Largest Free VMalloc Chunk", meminfo["VmallocTotal"] - meminfo["VmallocChunk"],
                meminfo["VmallocTotal"], params.get("levels_vmalloc"), of_what = "VMalloc Area", show_free=True)
        if r[0]:
            yield r # only display if non-OK

    hwc = meminfo.get("HardwareCorrupted")
    if hwc:
        yield params.get("handle_hw_corrupted_error", 2), "Hardware defect of %s" % get_bytes_human_readable(hwc)

    perfdata = []
    items = meminfo.items()
    items.sort()
    for name, value in items:
        if name.startswith("DirectMap"):
            continue
        if name.startswith("Vmalloc") and meminfo["VmallocTotal"] > 2**40: # useless on 64 Bit system
            continue
        if name.startswith("Huge"):
            if meminfo["HugePages_Total"] == 0: # omit useless data
                continue
            if name == "Hugepagesize":
                continue # not needed
            value = value * meminfo["Hugepagesize"] # convert number to actual memory size
        perfdata.append((camelcase_to_underscored(name.replace("(", "_").replace(")","")), value))
    yield 0, "", perfdata


check_info["mem.linux"] = {
    'inventory_function'        : inventory_mem_linux,
    'check_function'            : check_mem_linux,
    'service_description'       : 'Memory',
    'default_levels_variable'   : 'mem_linux_default_levels',
    'has_perfdata'              : True,
    'group'                     : 'memory_linux',
    "handle_real_time_checks"   : True,
    'includes'                  : [ 'mem.include' ],
}


def parse_proc_meminfo(info):
    return dict([ (i[0][:-1], int(i[1])) for i in info ])

mem_extended_perfdata = None

def inventory_mem_used(info):
    meminfo = parse_proc_meminfo(info)
    if "MemTotal" in meminfo \
        and "PageTotal" not in meminfo \
        and not is_linux_meminfo(meminfo): # handled by more modern check
        return [(None, {})]

def check_mem_used(_no_item, params, info):
    meminfo = parse_proc_meminfo(info)
    return check_memory(params, meminfo)

check_info['mem.used'] = {
    "check_function"          : check_mem_used,
    "inventory_function"      : inventory_mem_used,
    "service_description"     : "Memory used",
    "has_perfdata"            : True,
    "group"                   : "memory",
    "default_levels_variable" : "memory_default_levels",
    "includes"                : [ "mem.include" ],
    "handle_real_time_checks" : True,
}


factory_settings["memory_win_default_levels"] = {
    "memory"   : ( 80.0, 90.0 ),
    "pagefile" : ( 80.0, 90.0 ),
}


def inventory_mem_win(info):
    meminfo = parse_proc_meminfo(info)
    if "MemTotal" in meminfo and "PageTotal" in meminfo:
        return [(None, {})]


def check_mem_windows(item, params, info):
    meminfo = parse_proc_meminfo(info)
    MB = 1024.0 * 1024
    now = time.time()

    for title,             what,   paramname in [
        ("Memory usage",  "Mem",  "memory"),
        ("Commit Charge", "Page", "pagefile")]:

        key_total = what + "Total"
        key_free  = what + "Free"
        if not ( key_total in meminfo and key_free in meminfo ):
            continue

        total_kb = meminfo[key_total]
        free_kb  = meminfo[key_free]
        used_kb  = total_kb - free_kb
        used_mb  = used_kb / 1024.0
        free_mb  = free_kb / 1024.0
        perc     = 100.0 * used_kb / total_kb

        infotext = "%s: %.1f%% (%.1f/%.1f GB)" % \
                (title, perc, used_kb / MB, total_kb / MB)

        if type(params[paramname]) == tuple:
            warn, crit = params[paramname]

            if type(warn) == float:
                warn_kb = total_kb * warn / 100 / 1024
            else:
                warn_kb = warn * 1024

            if type(crit) == float:
                crit_kb = total_kb * crit / 100 / 1024
            else:
                crit_kb = crit * 1024

            perfdata = [(paramname, used_kb / 1024.0, warn_kb, crit_kb, 0, total_kb / 1024.0)]

        else:
            perfdata = [(paramname, used_kb / 1024.0, None, None, 0, total_kb / 1024.0)]

        if "average" in params:
            average_min = params["average"]
            used_kb = get_average("mem.win.%s" % paramname,
                                           now, used_kb, average_min, initialize_zero = False)
            used_mb  = used_kb / 1024.0
            free_mb  = (total_kb / 1024.0) - used_mb
            perc     = 100.0 * used_kb / total_kb
            infotext += ", %d min average: %.1f%% (%.1f GB)" % (average_min, perc, used_kb / MB)
            perfdata.append((paramname + "_avg", used_kb / 1024.0))

        if type(params[paramname]) == tuple:
            if (type(crit) == int and free_mb <= crit) or \
                (type(crit) == float and perc >= crit):
                state = 2
            elif (type(warn) == int and free_mb <= warn) or \
                (type(warn) == float and perc >= warn):
                state = 1
            else:
                state = 0

        else:
            state, infoadd, perfadd = check_levels(
                used_kb / 1024.0,                                            # Current value stored in MB in RRDs
                "average" in params and paramname + "_avg" or paramname,     # Name of RRD variable
                params[paramname],
                unit = "GB",                                                 # Levels are specified in GB...
                scale = 1024,                                                # ... in WATO ValueSpec
            )
            if infoadd:
                infotext += ", " + infoadd
            perfdata += perfadd

        yield state, infotext, perfdata


check_info["mem.win"] = {
    'check_function':          check_mem_windows,
    'inventory_function':      inventory_mem_win,
    'service_description':     'Memory and pagefile',
    'has_perfdata':            True,
    'group':                   'memory_pagefile_win',
    'default_levels_variable': 'memory_win_default_levels',
    "handle_real_time_checks" : True,
}


mem_vmalloc_default_levels = ( 80.0, 90.0, 64, 32 )

def inventory_mem_vmalloc(info):
    meminfo = parse_proc_meminfo(info)
    if is_linux_meminfo(meminfo):
        return # handled by new Linux memory check

    if "VmallocTotal" in meminfo and \
        not (meminfo["VmallocUsed"] == 0 and meminfo["VmallocChunk"] == 0):
        vmalloc = meminfo["VmallocTotal"] / 1024.4
        if vmalloc < 4096:
            return [ (None, "mem_vmalloc_default_levels") ]

def check_mem_vmalloc(item, params, info):
    meminfo = parse_proc_meminfo(info)
    total_mb = meminfo["VmallocTotal"] / 1024.0
    used_mb  = meminfo["VmallocUsed"] / 1024.0
    free_mb  = total_mb - used_mb
    chunk_mb = meminfo["VmallocChunk"] / 1024.0
    warn, crit, warn_chunk, crit_chunk = params

    state = 0
    infotxts = []
    perfdata = []
    for var, w, c, v, neg, what in [
        ( "used",  warn,       crit,       used_mb,  False, "used" ),
        ( "chunk", warn_chunk, crit_chunk, chunk_mb, True,  "largest chunk" )]:

        if type(w) == float:
            w_mb = total_mb * w / 100
        else:
            w_mb = float(w)

        if type(c) == float:
            c_mb = total_mb * c / 100
        else:
            c_mb = float(c)

        infotxt = "%s %.1f MB" % (what, v)
        if (v >= c_mb) != neg:
            s = 2
            infotxt += " (critical at %.1f MB!!)" % c_mb
        elif (v >= w_mb) != neg:
            s = 1
            infotxt += " (warning at %.1f MB!)" % w_mb
        else:
            s = 0
        state = max(state, s)
        infotxts.append(infotxt)
        perfdata.append( (var, v, w_mb, c_mb, 0, total_mb) )
    return (state, ("total %.1f MB, " % total_mb) + ", ".join(infotxts), perfdata)

check_info["mem.vmalloc"] = {
    'inventory_function':      inventory_mem_vmalloc,
    'check_function':          check_mem_vmalloc,
    'service_description':     'Vmalloc address space',
    'has_perfdata':            True,
    "handle_real_time_checks" : True,
}


convert_check_info()
clusters = {}
def is_cluster(hostname):
    return False

def clusters_of(hostname):
    return []

def is_snmp_host(hostname):
   return    False

def is_snmpv3_host(hostname):
   return  False

def is_tcp_host(hostname):
   return     True

def is_usewalk_host(hostname):
   return False

def snmpv3_contexts_of_host(hostname):
    return []

def is_inline_snmp_host(hostname):
   return        False

def snmp_proto_spec(hostname):
    return   ''

def snmp_port_spec(hostname):
    return   ''

def snmp_walk_command(hostname):
   return "snmpwalk -v1 -c 'public' -m '' -M '' -Cc"

ipaddresses = {'mgen1.gate.rtf': '192.168.4.3'}

def lookup_ip_address(hostname):
   return ipaddresses.get(hostname)

ipv6_primary_hosts = {'mgen1.gate.rtf': False}

def is_ipv6_primary(hostname):
   return ipv6_primary_hosts.get(hostname, False)

def get_datasource_program(hostname, ipaddress):
    return {'mgen1.gate.rtf': None}[hostname]

def host_is_aggregated(hostname):
    return False

def agent_port_of(hostname):
    return 6556

def exit_code_spec(hostname):
    return {}

def get_piggyback_translation(hostname):
    return {}

def agent_target_version(hostname):
    return None

def get_snmp_character_encoding(hostname):
    return None

nagios_illegal_chars = '`;~!$%^&*|\'"<>?,()='
cmctc_pcm_m_sensor_types = {72: 'kW', 73: 'kW', 74: 'hz', 75: 'V', 77: 'A', 79: 'kW', 80: 'kW'}
fc_port_admstates = {1: ('unknown', 1), 2: ('online', 0), 3: ('offline', 0), 4: ('bypassed', 1), 5: ('diagnostics', 1)}
fc_port_opstates = {1: ('unknown', 1), 2: ('unused', 1), 3: ('ready', 0), 4: ('warning', 1), 5: ('failure', 2), 6: ('not participating', 1), 7: ('initializing', 1), 8: ('bypass', 1), 9: ('ols', 0)}
fc_port_phystates = {1: ('unknown', 1), 2: ('failed', 2), 3: ('bypassed', 1), 4: ('active', 0), 5: ('loopback', 1), 6: ('txfault', 1), 7: ('no media', 1), 8: ('link down', 2)}
fc_port_no_inventory_types = [3]
fc_port_no_inventory_admstates = [1, 3]
fc_port_no_inventory_opstates = []
fc_port_no_inventory_phystates = []
fc_port_inventory_use_portname = False
ipmi_ignore_nr = False
ipmi_ignored_sensors = []
logwatch_dir = '/omd/sites/prod/var/check_mk/logwatch'
logwatch_max_filesize = 500000
logwatch_service_output = 'default'
netctr_counters = ['rx_bytes', 'tx_bytes', 'rx_packets', 'tx_packets', 'rx_errors', 'tx_errors', 'tx_collisions']
printer_alerts_text_map = {'Energiesparen': 0}
printer_supply_some_remaining_status = 1
winperf_cpu_default_levels = {'levels': (101.0, 101.0)}
winperf_msx_queues = {'Retry Remote Delivery': '4', 'Active Remote Delivery': '2', 'Poison Queue Length': '44', 'Active Mailbox Delivery': '6'}
try:
    sys.exit(do_check('mgen1.gate.rtf', '192.168.4.3'))
except SystemExit, e:
    sys.exit(e.code)
except Exception, e:
    import traceback, pprint
    sys.stdout.write("UNKNOWN - Exception in precompiled check: %s (details in long output)\n" % e)
    sys.stdout.write("Traceback: %s\n" % traceback.format_exc())

    l = file(log_dir + "/crashed-checks.log", "a")
    l.write(("Exception in precompiled check:\n"
            "  Check_MK Version: %s\n"
            "  Date:             %s\n"
            "  Host:             %s\n"
            "  %s\n") % (
            check_mk_version,
            time.strftime("%Y-%d-%m %H:%M:%S"),
            "mgen1.gate.rtf",
            traceback.format_exc().replace('\n', '\n      ')))
    l.close()
    sys.exit(3)
