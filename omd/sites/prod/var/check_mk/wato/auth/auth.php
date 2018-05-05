<?php
// Created by Multisite UserDB Hook (users-saved)
global $mk_users, $mk_roles, $mk_groups, $mk_folders;
$mk_users   = array(
    'omdadmin' => array(
        'locked' => false,
        'language' => null,
        'roles' => array(
            'admin',
        ),
        'last_pw_change' => 1485442262,
        'num_failed' => 1,
        'alias' => 'omdadmin',
        'enforce_pw_change' => false,
        'serial' => 0,
        'password' => 'M29dfyFjgy5iA',
    ),
);
$mk_roles   = array(
    'admin' => array(
        'general.use',
        'general.see_all',
        'general.edit_views',
        'general.publish_views',
        'general.see_user_views',
        'general.force_views',
        'general.delete_foreign_views',
        'general.edit_dashboards',
        'general.publish_dashboards',
        'general.see_user_dashboards',
        'general.force_dashboards',
        'general.delete_foreign_dashboards',
        'general.view_option_columns',
        'general.view_option_refresh',
        'general.painter_options',
        'general.act',
        'general.see_sidebar',
        'general.configure_sidebar',
        'general.edit_profile',
        'general.edit_notifications',
        'general.disable_notifications',
        'general.edit_user_attributes',
        'general.change_password',
        'general.logout',
        'general.ignore_soft_limit',
        'general.ignore_hard_limit',
        'general.acknowledge_werks',
        'general.notify',
        'general.edit_bookmark_list',
        'general.publish_bookmark_list',
        'general.see_user_bookmark_list',
        'general.force_bookmark_list',
        'general.edit_foreign_bookmark_list',
        'general.delete_foreign_bookmark_list',
        'sidesnap.wiki',
        'sidesnap.wato_folders',
        'sidesnap.custom_links',
        'sidesnap.nagios_legacy',
        'sidesnap.dashboards',
        'sidesnap.admin_mini',
        'sidesnap.bookmarks',
        'sidesnap.speedometer',
        'sidesnap.biaggr_groups',
        'sidesnap.tactical_overview',
        'sidesnap.master_control',
        'sidesnap.sitestatus',
        'sidesnap.wato_foldertree',
        'sidesnap.performance',
        'sidesnap.mkeventd_performance',
        'sidesnap.problem_hosts',
        'sidesnap.nagvis_maps',
        'sidesnap.views',
        'sidesnap.hostgroups',
        'sidesnap.search',
        'sidesnap.hostmatrix',
        'sidesnap.about',
        'sidesnap.tag_tree',
        'sidesnap.admin',
        'sidesnap.servicegroups',
        'sidesnap.hosts',
        'sidesnap.time',
        'wato.api_allowed',
        'wato.use',
        'wato.edit',
        'wato.seeall',
        'wato.activate',
        'wato.activateforeign',
        'wato.auditlog',
        'wato.hosts',
        'wato.edit_hosts',
        'wato.parentscan',
        'wato.move_hosts',
        'wato.rename_hosts',
        'wato.manage_hosts',
        'wato.diag_host',
        'wato.clone_hosts',
        'wato.update_dns_cache',
        'wato.services',
        'wato.edit_folders',
        'wato.manage_folders',
        'wato.see_all_folders',
        'wato.all_folders',
        'wato.hosttags',
        'wato.global',
        'wato.rulesets',
        'wato.groups',
        'wato.timeperiods',
        'wato.sites',
        'wato.automation',
        'wato.users',
        'wato.notifications',
        'wato.snapshots',
        'wato.pattern_editor',
        'wato.icons',
        'wato.download_agents',
        'wato.download_agent_output',
        'wato.bi_rules',
        'wato.bi_admin',
        'mkeventd.config',
        'mkeventd.edit',
        'mkeventd.activate',
        'mkeventd.switchmode',
        'nagvis.*_*_*',
        'action.reschedule',
        'action.notifications',
        'action.enablechecks',
        'action.clearmodattr',
        'action.fakechecks',
        'action.customnotification',
        'action.acknowledge',
        'action.addcomment',
        'action.downtimes',
        'action.star',
        'mkeventd.seeall',
        'mkeventd.seeunrelated',
        'mkeventd.update',
        'mkeventd.update_comment',
        'mkeventd.update_contact',
        'mkeventd.changestate',
        'mkeventd.actions',
        'mkeventd.delete',
        'view.invswpac_of_host',
        'view.mobile_notifications',
        'view.aggr_service',
        'view.ec_events_of_host',
        'view.hostgroupservices',
        'view.searchpnp',
        'view.starred_services',
        'view.inv_hosts_ports',
        'view.hosttiles',
        'view.nagstamon_hosts',
        'view.servicegroup',
        'view.allhosts',
        'view.hostevents',
        'view.aggr_single_api',
        'view.downtimes_of_host',
        'view.searchsvc',
        'view.aggr_hostgroup_boxed',
        'view.host_pending',
        'view.invinterface_search',
        'view.downtime_history',
        'view.aggr_all',
        'view.mobile_svcproblems_unack',
        'view.hoststatus',
        'view.comments_of_service',
        'view.servicedesc',
        'view.problemsofhost',
        'view.hostgroupgrid',
        'view.mobile_hostproblems',
        'view.mobile_hostsvcevents',
        'view.notifications',
        'view.svcbygroups',
        'view.comments_of_host',
        'view.host_crit',
        'view.host_unknown',
        'view.ec_history_of_host',
        'view.logfile',
        'view.nagstamon_svc',
        'view.ec_history_of_event',
        'view.hostpnp',
        'view.sitesvcs',
        'view.mobile_svcproblems',
        'view.aggr_summary',
        'view.perf_matrix_search',
        'view.mobile_contactnotifications',
        'view.host_export',
        'view.ec_events_mobile',
        'view.hostgroup',
        'view.svc_dt_hist',
        'view.ec_historyentry',
        'view.api_downtimes',
        'view.mobile_events',
        'view.hosts',
        'view.uncheckedsvc',
        'view.aggr_singlehosts',
        'view.inv_host_history',
        'view.downtimes_of_service',
        'view.allservices',
        'view.host_dt_hist',
        'view.mobile_hostsvcnotifications',
        'view.servicedescpnp',
        'view.ec_history_recent',
        'view.invswpac_search',
        'view.hostgroups',
        'view.svcproblems',
        'view.inv_host',
        'view.mobile_svcevents',
        'view.starred_hosts',
        'view.sitehosts',
        'view.aggr_group',
        'view.hostproblems',
        'view.searchhost',
        'view.hostsvcevents',
        'view.inv_hosts_cpu',
        'view.svcproblems_dash',
        'view.mobile_hostproblems_unack',
        'view.downtimes',
        'view.hostproblems_dash',
        'view.aggr_host',
        'view.comments',
        'view.aggr_problems',
        'view.mobile_hoststatus',
        'view.hostnotifications',
        'view.host_warn',
        'view.aggr_all_api',
        'view.svcbyhgroups',
        'view.contactnotifications',
        'view.events',
        'view.events_dash',
        'view.ec_events',
        'view.host_ok',
        'view.ec_event',
        'view.mobile_searchsvc',
        'view.hostsvcnotifications',
        'view.mobile_searchhost',
        'view.aggr_hostnameaggrs',
        'view.host',
        'view.pendingsvc',
        'view.mobile_svcnotifications',
        'view.hostsbygroup',
        'view.mobile_host',
        'view.ec_event_mobile',
        'view.service',
        'view.svcgroups',
        'view.aggr_hostproblems',
        'view.svcnotifications',
        'view.alertstats',
        'view.allhosts_mini',
        'view.recentsvc',
        'view.aggr_singlehost',
        'view.perf_matrix',
        'view.aggr_single',
        'view.mobile_service',
        'view.invinterface_of_host',
        'view.svcevents',
        'view.ec_events_of_monhost',
        'view.svcgroups_grid',
        'bi.see_all',
        'dashboard.simple_problems',
        'dashboard.main',
        'dashboard.topology',
    ),
    'user' => array(
        'general.use',
        'general.edit_views',
        'general.publish_views',
        'general.see_user_views',
        'general.edit_dashboards',
        'general.publish_dashboards',
        'general.see_user_dashboards',
        'general.view_option_columns',
        'general.view_option_refresh',
        'general.painter_options',
        'general.act',
        'general.see_sidebar',
        'general.configure_sidebar',
        'general.edit_profile',
        'general.edit_notifications',
        'general.edit_user_attributes',
        'general.change_password',
        'general.logout',
        'general.ignore_soft_limit',
        'general.edit_bookmark_list',
        'general.publish_bookmark_list',
        'general.see_user_bookmark_list',
        'sidesnap.wiki',
        'sidesnap.wato_folders',
        'sidesnap.custom_links',
        'sidesnap.nagios_legacy',
        'sidesnap.dashboards',
        'sidesnap.admin_mini',
        'sidesnap.bookmarks',
        'sidesnap.biaggr_groups',
        'sidesnap.tactical_overview',
        'sidesnap.sitestatus',
        'sidesnap.wato_foldertree',
        'sidesnap.problem_hosts',
        'sidesnap.nagvis_maps',
        'sidesnap.views',
        'sidesnap.hostgroups',
        'sidesnap.search',
        'sidesnap.hostmatrix',
        'sidesnap.about',
        'sidesnap.tag_tree',
        'sidesnap.admin',
        'sidesnap.servicegroups',
        'sidesnap.hosts',
        'sidesnap.time',
        'wato.api_allowed',
        'wato.use',
        'wato.edit',
        'wato.activate',
        'wato.hosts',
        'wato.edit_hosts',
        'wato.parentscan',
        'wato.move_hosts',
        'wato.manage_hosts',
        'wato.diag_host',
        'wato.clone_hosts',
        'wato.update_dns_cache',
        'wato.services',
        'wato.edit_folders',
        'wato.manage_folders',
        'wato.rulesets',
        'wato.pattern_editor',
        'wato.download_agents',
        'wato.bi_rules',
        'nagvis.Map_view',
        'nagvis.Map_edit',
        'nagvis.Map_delete',
        'action.reschedule',
        'action.customnotification',
        'action.acknowledge',
        'action.addcomment',
        'action.downtimes',
        'action.star',
        'mkeventd.seeall',
        'mkeventd.seeunrelated',
        'mkeventd.update',
        'mkeventd.update_comment',
        'mkeventd.update_contact',
        'mkeventd.changestate',
        'mkeventd.actions',
        'mkeventd.delete',
        'view.invswpac_of_host',
        'view.mobile_notifications',
        'view.aggr_service',
        'view.ec_events_of_host',
        'view.hostgroupservices',
        'view.searchpnp',
        'view.starred_services',
        'view.inv_hosts_ports',
        'view.hosttiles',
        'view.nagstamon_hosts',
        'view.servicegroup',
        'view.allhosts',
        'view.hostevents',
        'view.aggr_single_api',
        'view.downtimes_of_host',
        'view.searchsvc',
        'view.aggr_hostgroup_boxed',
        'view.host_pending',
        'view.invinterface_search',
        'view.downtime_history',
        'view.aggr_all',
        'view.mobile_svcproblems_unack',
        'view.hoststatus',
        'view.comments_of_service',
        'view.servicedesc',
        'view.problemsofhost',
        'view.hostgroupgrid',
        'view.mobile_hostproblems',
        'view.mobile_hostsvcevents',
        'view.notifications',
        'view.svcbygroups',
        'view.comments_of_host',
        'view.host_crit',
        'view.host_unknown',
        'view.ec_history_of_host',
        'view.logfile',
        'view.nagstamon_svc',
        'view.ec_history_of_event',
        'view.hostpnp',
        'view.sitesvcs',
        'view.mobile_svcproblems',
        'view.aggr_summary',
        'view.perf_matrix_search',
        'view.mobile_contactnotifications',
        'view.host_export',
        'view.ec_events_mobile',
        'view.hostgroup',
        'view.svc_dt_hist',
        'view.ec_historyentry',
        'view.api_downtimes',
        'view.mobile_events',
        'view.hosts',
        'view.uncheckedsvc',
        'view.aggr_singlehosts',
        'view.inv_host_history',
        'view.downtimes_of_service',
        'view.allservices',
        'view.host_dt_hist',
        'view.mobile_hostsvcnotifications',
        'view.servicedescpnp',
        'view.ec_history_recent',
        'view.invswpac_search',
        'view.hostgroups',
        'view.svcproblems',
        'view.inv_host',
        'view.mobile_svcevents',
        'view.starred_hosts',
        'view.sitehosts',
        'view.aggr_group',
        'view.hostproblems',
        'view.searchhost',
        'view.hostsvcevents',
        'view.inv_hosts_cpu',
        'view.svcproblems_dash',
        'view.mobile_hostproblems_unack',
        'view.downtimes',
        'view.hostproblems_dash',
        'view.aggr_host',
        'view.comments',
        'view.aggr_problems',
        'view.mobile_hoststatus',
        'view.hostnotifications',
        'view.host_warn',
        'view.aggr_all_api',
        'view.svcbyhgroups',
        'view.contactnotifications',
        'view.events',
        'view.events_dash',
        'view.ec_events',
        'view.host_ok',
        'view.ec_event',
        'view.mobile_searchsvc',
        'view.hostsvcnotifications',
        'view.mobile_searchhost',
        'view.aggr_hostnameaggrs',
        'view.host',
        'view.pendingsvc',
        'view.mobile_svcnotifications',
        'view.hostsbygroup',
        'view.mobile_host',
        'view.ec_event_mobile',
        'view.service',
        'view.svcgroups',
        'view.aggr_hostproblems',
        'view.svcnotifications',
        'view.alertstats',
        'view.allhosts_mini',
        'view.recentsvc',
        'view.aggr_singlehost',
        'view.perf_matrix',
        'view.aggr_single',
        'view.mobile_service',
        'view.invinterface_of_host',
        'view.svcevents',
        'view.ec_events_of_monhost',
        'view.svcgroups_grid',
        'dashboard.simple_problems',
        'dashboard.main',
        'dashboard.topology',
    ),
    'guest' => array(
        'general.use',
        'general.see_all',
        'general.see_user_views',
        'general.see_user_dashboards',
        'general.view_option_columns',
        'general.painter_options',
        'general.see_sidebar',
        'general.logout',
        'general.see_user_bookmark_list',
        'sidesnap.wiki',
        'sidesnap.wato_folders',
        'sidesnap.custom_links',
        'sidesnap.nagios_legacy',
        'sidesnap.dashboards',
        'sidesnap.bookmarks',
        'sidesnap.biaggr_groups',
        'sidesnap.tactical_overview',
        'sidesnap.wato_foldertree',
        'sidesnap.problem_hosts',
        'sidesnap.nagvis_maps',
        'sidesnap.views',
        'sidesnap.hostgroups',
        'sidesnap.search',
        'sidesnap.hostmatrix',
        'sidesnap.about',
        'sidesnap.tag_tree',
        'sidesnap.servicegroups',
        'sidesnap.hosts',
        'sidesnap.time',
        'wato.api_allowed',
        'wato.download_agents',
        'nagvis.Rotation_view_*',
        'nagvis.Map_view_*',
        'mkeventd.seeall',
        'mkeventd.seeunrelated',
        'view.invswpac_of_host',
        'view.mobile_notifications',
        'view.aggr_service',
        'view.ec_events_of_host',
        'view.hostgroupservices',
        'view.searchpnp',
        'view.starred_services',
        'view.inv_hosts_ports',
        'view.hosttiles',
        'view.nagstamon_hosts',
        'view.servicegroup',
        'view.allhosts',
        'view.hostevents',
        'view.aggr_single_api',
        'view.downtimes_of_host',
        'view.searchsvc',
        'view.aggr_hostgroup_boxed',
        'view.host_pending',
        'view.invinterface_search',
        'view.downtime_history',
        'view.aggr_all',
        'view.mobile_svcproblems_unack',
        'view.hoststatus',
        'view.comments_of_service',
        'view.servicedesc',
        'view.problemsofhost',
        'view.hostgroupgrid',
        'view.mobile_hostproblems',
        'view.mobile_hostsvcevents',
        'view.notifications',
        'view.svcbygroups',
        'view.comments_of_host',
        'view.host_crit',
        'view.host_unknown',
        'view.ec_history_of_host',
        'view.logfile',
        'view.nagstamon_svc',
        'view.ec_history_of_event',
        'view.hostpnp',
        'view.sitesvcs',
        'view.mobile_svcproblems',
        'view.aggr_summary',
        'view.perf_matrix_search',
        'view.mobile_contactnotifications',
        'view.host_export',
        'view.ec_events_mobile',
        'view.hostgroup',
        'view.svc_dt_hist',
        'view.ec_historyentry',
        'view.api_downtimes',
        'view.mobile_events',
        'view.hosts',
        'view.uncheckedsvc',
        'view.aggr_singlehosts',
        'view.inv_host_history',
        'view.downtimes_of_service',
        'view.allservices',
        'view.host_dt_hist',
        'view.mobile_hostsvcnotifications',
        'view.servicedescpnp',
        'view.ec_history_recent',
        'view.invswpac_search',
        'view.hostgroups',
        'view.svcproblems',
        'view.inv_host',
        'view.mobile_svcevents',
        'view.starred_hosts',
        'view.sitehosts',
        'view.aggr_group',
        'view.hostproblems',
        'view.searchhost',
        'view.hostsvcevents',
        'view.inv_hosts_cpu',
        'view.svcproblems_dash',
        'view.mobile_hostproblems_unack',
        'view.downtimes',
        'view.hostproblems_dash',
        'view.aggr_host',
        'view.comments',
        'view.aggr_problems',
        'view.mobile_hoststatus',
        'view.hostnotifications',
        'view.host_warn',
        'view.aggr_all_api',
        'view.svcbyhgroups',
        'view.contactnotifications',
        'view.events',
        'view.events_dash',
        'view.ec_events',
        'view.host_ok',
        'view.ec_event',
        'view.mobile_searchsvc',
        'view.hostsvcnotifications',
        'view.mobile_searchhost',
        'view.aggr_hostnameaggrs',
        'view.host',
        'view.pendingsvc',
        'view.mobile_svcnotifications',
        'view.hostsbygroup',
        'view.mobile_host',
        'view.ec_event_mobile',
        'view.service',
        'view.svcgroups',
        'view.aggr_hostproblems',
        'view.svcnotifications',
        'view.alertstats',
        'view.allhosts_mini',
        'view.recentsvc',
        'view.aggr_singlehost',
        'view.perf_matrix',
        'view.aggr_single',
        'view.mobile_service',
        'view.invinterface_of_host',
        'view.svcevents',
        'view.ec_events_of_monhost',
        'view.svcgroups_grid',
        'bi.see_all',
        'dashboard.simple_problems',
        'dashboard.main',
        'dashboard.topology',
    ),
);
$mk_groups  = array(
);
$mk_folders = array(
);

function get_folder_permissions($username) {
    global $mk_folders;
    if(!isset($mk_folders[$username])) {
        return array();
    } else {
        $permissions = $mk_folders[$username];
        foreach ($permissions as $folder => $perms) {
            if (!isset($perms['read']))
                $perms['read'] = false;
            elseif (!isset($perms['write']))
                $perms['write'] = false;
        }
        return $permissions;
    }
}

function all_users() {
    global $mk_users;
    return $mk_users;
}

function user_roles($username) {
    global $mk_users;
    if(!isset($mk_users[$username]))
        return array();
    else
        return $mk_users[$username]['roles'];
}

function user_groups($username) {
    global $mk_users;
    if(!isset($mk_users[$username]) || !isset($mk_users[$username]['contactgroups']))
        return array();
    else
        return $mk_users[$username]['contactgroups'];
}

function user_permissions($username) {
    global $mk_roles;
    $permissions = array();

    foreach(user_roles($username) AS $role)
        $permissions = array_merge($permissions, $mk_roles[$role]);

    // Make the array uniq
    array_flip($permissions);
    array_flip($permissions);

    return $permissions;
}

function users_with_role($want_role) {
    global $mk_users, $mk_roles;
    $result = array();
    foreach($mk_users AS $username => $user) {
        foreach($user['roles'] AS $role) {
            if($want_role == $role) {
                $result[] = $username;
            }
        }
    }
    return $result;
}

function roles_with_permission($want_permission) {
    global $mk_roles;
    $result = array();
    foreach($mk_roles AS $rolename => $role) {
        foreach($role AS $permission) {
            if($permission == $want_permission) {
                $result[] = $rolename;
                break;
            }
        }
    }
    return $result;
}

function users_with_permission($need_permission) {
    global $mk_users;
    $result = array();
    foreach(roles_with_permission($need_permission) AS $rolename) {
        $result = array_merge($result, users_with_role($rolename));
    }
    return $result;
}

function may($username, $need_permission) {
    global $mk_roles;
    foreach(user_roles($username) AS $role) {
        foreach($mk_roles[$role] AS $permission) {
            if($need_permission == $permission) {
                return true;
            }
        }
    }
    return false;
}

function permitted_maps($username) {
    global $mk_groups;
    $maps = array();
    foreach (user_groups($username) AS $groupname) {
        if (isset($mk_groups[$groupname])) {
            foreach ($mk_groups[$groupname] AS $mapname) {
                $maps[$mapname] = null;
            }
        }
    }
    return array_keys($maps);
}

?>