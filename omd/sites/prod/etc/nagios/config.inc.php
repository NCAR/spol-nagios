<?php
// This file exists per site and configures site specific paths for
// Nagios' web pages


$cfg['cgi_config_file']='/omd/sites/prod/etc/nagios/cgi.cfg';  // location of the CGI config file

$cfg['cgi_base_url']='/prod/nagios/cgi-bin';


// FILE LOCATION DEFAULTS
$cfg['main_config_file']='/omd/sites/prod/tmp/nagios/nagios.cfg';  // default location of the main Nagios config file
$cfg['status_file']='/omd/sites/prod/tmp/nagios/status.dat'; // default location of Nagios status file
$cfg['state_retention_file']='/omd/sites/prod/var/nagios/retention.dat'; // default location of Nagios retention file



// utilities
require_once('/omd/sites/prod/share/nagios/htdocs/includes/utils.inc.php');

?>
