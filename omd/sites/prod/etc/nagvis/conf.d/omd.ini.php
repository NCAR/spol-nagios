; <?php return 1; ?>
; -----------------------------------------------------------------
; Don't touch this file. It is under control of OMD. Modifying this
; file might break the update mechanism of OMD.
;
; If you want to customize your NagVis configuration please use the
; etc/nagvis/nagvis.ini.php file.
; -----------------------------------------------------------------

[global]
sesscookiepath="/prod/nagvis"
authorisation_group_perms_file="/omd/sites/prod/etc/nagvis/perms.db"

[paths]
base="/omd/sites/prod/share/nagvis/"
local_base="/omd/sites/prod/local/share/nagvis/"
cfg="/omd/sites/prod/etc/nagvis/"
mapcfg="/omd/sites/prod/etc/nagvis/maps/"
geomap="/omd/sites/prod/etc/nagvis/geomap/"
var="/omd/sites/prod/tmp/nagvis/"
sharedvar="/omd/sites/prod/tmp/nagvis/share/"
profiles="/omd/sites/prod/var/nagvis/profiles/"
htmlbase="/prod/nagvis"
local_htmlbase="/prod/nagvis/local"
htmlcgi="/prod/nagios/cgi-bin"

[defaults]
backend="prod"

[backend_prod]
backendtype="mklivestatus"
socket="unix:/omd/sites/prod/tmp/run/live"
