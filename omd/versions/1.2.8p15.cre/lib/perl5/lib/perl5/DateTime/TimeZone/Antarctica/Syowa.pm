# This file is auto-generated by the Perl DateTime Suite time zone
# code generator (0.07) This code generator comes with the
# DateTime::TimeZone module distribution in the tools/ directory

#
# Generated from /tmp/8FT049ktOU/antarctica.  Olson data version 2015d
#
# Do not edit this file directly.
#
package DateTime::TimeZone::Antarctica::Syowa;
$DateTime::TimeZone::Antarctica::Syowa::VERSION = '1.88';
use strict;

use Class::Singleton 1.03;
use DateTime::TimeZone;
use DateTime::TimeZone::OlsonDB;

@DateTime::TimeZone::Antarctica::Syowa::ISA = ( 'Class::Singleton', 'DateTime::TimeZone' );

my $spans =
[
    [
DateTime::TimeZone::NEG_INFINITY, #    utc_start
61727875200, #      utc_end 1957-01-29 00:00:00 (Tue)
DateTime::TimeZone::NEG_INFINITY, #  local_start
61727875200, #    local_end 1957-01-29 00:00:00 (Tue)
0,
0,
'zzz',
    ],
    [
61727875200, #    utc_start 1957-01-29 00:00:00 (Tue)
DateTime::TimeZone::INFINITY, #      utc_end
61727886000, #  local_start 1957-01-29 03:00:00 (Tue)
DateTime::TimeZone::INFINITY, #    local_end
10800,
0,
'SYOT',
    ],
];

sub olson_version {'2015d'}

sub has_dst_changes {0}

sub _max_year {2025}

sub _new_instance {
    return shift->_init( @_, spans => $spans );
}



1;

