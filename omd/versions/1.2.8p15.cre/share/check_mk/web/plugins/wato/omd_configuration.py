#!/usr/bin/python
# -*- encoding: utf-8; py-indent-offset: 4 -*-
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4
#
#       U  ___ u  __  __   ____
#        \/"_ \/U|' \/ '|u|  _"\
#        | | | |\| |\/| |/| | | |
#    .-,_| |_| | | |  | |U| |_| |\
#     \_)-\___/  |_|  |_| |____/ u
#          \\   <<,-,,-.   |||_
#         (__)   (./  \.) (__)_)
#
# This file is part of OMD - The Open Monitoring Distribution.
# The official homepage is at <http://omdistro.org>.
#
# OMD  is  free software;  you  can  redistribute it  and/or modify it
# under the  terms of the  GNU General Public License  as published by
# the  Free Software  Foundation  in  version 2.  OMD  is  distributed
# in the hope that it will be useful, but WITHOUT ANY WARRANTY;  with-
# out even the implied warranty of  MERCHANTABILITY  or  FITNESS FOR A
# PARTICULAR PURPOSE. See the  GNU General Public License for more de-
# ails.  You should have  received  a copy of the  GNU  General Public
# License along with GNU Make; see the file  COPYING.  If  not,  write
# to the Free Software Foundation, Inc., 51 Franklin St,  Fifth Floor,
# Boston, MA 02110-1301 USA.

# needs to be moved to official omd once Check_MK 1.2.3/1.2.4 is included

diskspace_config = defaults.omd_root + '/etc/diskspace.conf'

def diskspace_load(settings):
    execfile(diskspace_config, settings, settings)

def diskspace_save(settings):
    f = file(diskspace_config, 'w')
    for k, v in settings.items():
        f.write('%s = %r\n' % (k, v))

register_configvar_domain('diskspace', load = diskspace_load, save = diskspace_save)
group = _('Site Management')

register_configvar(group,
    "max_file_age",
    Optional(
        Age(
            minvalue = 1, # 1 sec
            default_value = 31536000, # 1 year
        ),
        title = _('Delete files older than'),
        help = _("The historic events (state changes, downtimes etc.) of your hosts and services "
                 "is stored in the monitoring "
                 "history as plain text log files. One history log file contains the monitoring "
                 "history of a given time period of all hosts and services. The files which are "
                 "older than the configured time will be removed on the next execution of the "
                 "diskspace cleanup.<br>"
                 "The historic metrics are stored in files for each host and service "
                 "individually. When a host or service is removed from the monitoring, it's "
                 "metric files remain untouched on your disk until the files last update "
                 "(modification time) is longer ago than the configure age."),
    ),
    domain = 'diskspace'
)

register_configvar(group,
    "min_free_bytes",
    Optional(
        Filesize(
            minvalue = 1, # min 1 byte
            default_value = 0,
        ),
        title = _('Delete additional files when diskspace is below'),
        help = _("When the disk space cleanup by file age is not sufficient to clean gain enough "
                 "free disk space, then the cleanup mechanism starts cleaning up additional "
                 "files. The files are deleted by age, the oldest first, until the files are "
                 "newer than the configured minimum file age."),
    ),
    domain = 'diskspace'
)

register_configvar(group,
    "min_file_age",
    Optional(
        Age(
            minvalue = 1, # minimum 1 sec
            default_value = 0,
        ),
        title = _('Never remove files newer than'),
        help = _("With this option you can prevent cleanup of files which have been updated "
                 "within this time range."),
    ),
    domain = 'diskspace'
)
