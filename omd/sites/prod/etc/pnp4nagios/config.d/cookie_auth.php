<?php
// Created by OMD hook MULTISITE_COOKIE_AUTH
//
// Using the multisite cookie based authentication when no
// REMOTE_USER available.
//
$conf['auth_multisite_enabled']    = TRUE;
$conf['auth_multisite_htpasswd']   = '/omd/sites/prod/etc/htpasswd';
$conf['auth_multisite_secret']     = '/omd/sites/prod/etc/auth.secret';
$conf['auth_multisite_serials']    = '/omd/sites/prod/etc/auth.serials';
$conf['auth_multisite_login_url']  = '/prod/check_mk/login.py';
?>
