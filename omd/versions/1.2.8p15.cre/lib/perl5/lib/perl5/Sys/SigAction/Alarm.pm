
package Sys::SigAction::Alarm;
require 5.005;
use strict;
#use warnings;
use vars qw( @ISA @EXPORT_OK );
require Exporter;
@ISA = qw( Exporter );
@EXPORT_OK = qw( ssa_alarm );
my $have_hires = scalar eval 'use Time::HiRes; Time::HiRes::ualarm(0); 1;';
use POSIX qw( INT_MAX ceil ) ;
my $hrworks; 
sub ssa_alarm($)
{
   my $secs = shift;
   #print  print "secs=$secs\n";

   if ( $hrworks and ($secs le (INT_MAX()/1_000_000.0) ) )
   {
      Time::HiRes::ualarm( $secs * 1_000_000 );
   }
   else
   {
      alarm( ceil( $secs ) );
   }
}

sub hires_works { return $hrworks; }; #test support

$hrworks = 1; 1;
