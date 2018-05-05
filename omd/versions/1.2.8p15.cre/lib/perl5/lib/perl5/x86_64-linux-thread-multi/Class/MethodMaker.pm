# (X)Emacs mode: -*- cperl -*-

package Class::MethodMaker;

use Class::MethodMaker::Constants qw( );
use Class::MethodMaker::Engine    qw();

# Make this line self-contained so MakeMaker can eval() it.
our $VERSION = '2.22';
our $PACKAGE = 'Class-MethodMaker';

use XSLoader qw();
XSLoader::load 'Class::MethodMaker', $VERSION;

sub AUTOLOAD {
  ($x = $AUTOLOAD) =~ s/^Class::MethodMaker/Class::MethodMaker::Engine/;
  goto &$x(@_);
}

sub import { Class::MethodMaker::Engine->import(@_[1..$#_]) }

sub INTEGER() { Class::MethodMaker::Constants::INTEGER() }

1; # keep require happy

__END__

=head1 NAME

Class::MethodMaker - Create generic methods for OO Perl

=head1 SYNOPSIS

  use Class::MethodMaker
    [ scalar => [qw/ foo bar baz /],
      new    => [qw/ new /]        ,
    ];

=head1 DESCRIPTION

This module solves the problem of having to continually write accessor
methods for your objects that perform standard tasks.

The argument to 'use' is an B<arrayref>, as pairs whose "keys" are the names
of types of generic methods generated by MethodMaker and whose "values" tell
method maker what methods to make.

To override any generated methods, it is sufficient to ensure that the
overriding method is defined when Class::MethodMaker is called.  Note
that the C<use> keyword introduces a C<BEGIN> block, so you may need to
define (or at least declare) your overriding method in a C<BEGIN> block.

=head2 Simple Use

A simple class made with C<Class::MethodMaker> looks like this:

  package MyClass;

  use Class::MethodMaker
    [ scalar => [qw/ name /],
      new    => [qw/ new  /],
    ];

This creates a class, of which new instances may be created using C<new>, each
with a single scalar component called C<name>.  Name may be queried and (re)set
using the methods C<name>, C<name_reset> and C<name_isset>:

  package main;

  my $m = MyClass->new;
  my $n;
  $\ = "\n";

  print $m->name_isset ? "true" : "false";     # false

  $m->name("foo");
  $n = $m->name;
  print defined $n ? "->$n<-" : "*undef*";     # ->foo<-
  print $m->name_isset ? "true" : "false";     # true

  $m->name(undef);
  $n = $m->name;
  print defined $n ? "->$n<-" : "*undef*";     # *undef*
  print $m->name_isset ? "true" : "false";     # true

  $m->name_reset;
  $n = $m->name;
  print defined $n ? "->$n<-" : "*undef*";     # *undef*
  print $m->name_isset ? "true" : "false";     # false

The available component types are L<scalar|Class::MethodMaker::scalar>,
L<array|Class::MethodMaker::array>, L<hash|Class::MethodMaker::hash>.  Certain
non-data-type utilities are also provided:
L<new|Class::MethodMaker::Engine/new>, for constructors,
L<deep_copy|Class::MethodMaker::Engine/deep_copy> and
L<copy|Class::MethodMaker::Engine/copy> for object copies, and
L<abstract|Class::MethodMaker::Engine/abstract> for creating abstract methods.

Each of the components take common options.  These include L<-static>, for
per-class rather than per-instance data, L<-type>, to restrict the data stored
to certain types (e.g., objects of a certain class), L<-forward> to forward
(proxy) given methods onto components, L<-default>/L<-default_ctor> to set
default values for components, L<-tie_class> to tie the storage of a data type
to a given class, L<-read_cb>/L<-store_cb> to call user-defined functions on
read/store (without the overhead/complexity of ties; and allowing callbacks on
existing tie classes).

=head2 Detailed Use

C<Class::MethodMaker> installs I<components> into a class, by means of methods
that interrogate and amend those components.  A component, sometimes referred
in other documentation as a I<slot> is a group of one or more attributes
(variables) that are associated with an instance of a class (sometimes called
an object), or occasionally a class itself (often referred to as a I<static>
component).  A component is intended as a cohesive unit of data that should
only normally be interrogated or set through the methods provided.

Given an instance of a class where each instance represents a car, examples of
components are the C<make> and C<model> (each of which would be a simple
scalar, a string), the engine (a simple scalar, an instance of
Engine::Combustion), and the wheels (an array of instances of Wheel).  Note
that the wheels form one component, an array.  Of course, the implementor
might instead choose to use four components, each being a scalar wheel.

To have the components created, the principle use of Class::MethodMaker is to
specify the type (data-structure) and name of each component to the import
method of Class::MethodMaker

  package MyClass;

  use Class::MethodMaker
    [ scalar => 'name',
      new    => [qw/ new /],
    ];

In this example, the import is called implicitly via the C<use> statement.
The components are installed in the package in effect where the import is
called.  The argument to import is arranged as pairs, where the first of each
pair is the type of the data-structure, the second is the arguments for that
data-structure; in the most simple case, the name of a component to install
using that data-structure.  The second of the pair should be an arrayref if
not a simple name.

Data-structures may be repeated in the call:

  use Class::MethodMaker
    [ scalar => 'name1',
      new    => [qw/ new /],
      scalar => 'name2',
    ];

It is an error to attempt to install a two or more components with the same
name twice.

Options may be given to data structures to amend the nature and behaviour of
the components created.  Some options are common across all data structure
(e.g., C<static>) whilst some are specific to their respective data
structures.  Option syntax is laid out in detail below.  In simple, options
are provided by way of hashrefs from option name to option value.  Options and
component names are order-sensitive; options appearing after a component do
not affect that component.  Options only apply to the data-structure to which
they are specified.  B<Boolean> options (e.g., static) may be abbreviated to
-option to set, !option to unset, without a hashref.

  use Class::MethodMaker
    [ scalar => [+{ -type => 'File::stat' }, qw/ -static name /],
      new    => 'new',
    ];

There are also non-data-structure methods that may be created by
Class::MethodMaker.  C<new> is an example of one such value; it instead causes
a standard C<new> method to be created for the calling class.  The arguments
and options syntax remains the same, but many options clearly do not apply
(e.g., C<type> for C<new>).

=head2 Interaction with Superclasses

Basically, C<Class::MethodMaker> takes no notice of class hierarchies.  If you
choose to install a component x in a class B that is a subclass of class A
that already has a component x, then the methods addressing x in B will simply
override those in class A in the usual fashion.  C<Class::MethodMaker> takes
no special action for this situation.  This is a feature.

=head2 Option Syntax

The arguments to Class::MethodMaker are passed in a single arrayref, as pairs,
with the first of each pair being the name of the data-structure, and the
second being the arguments to that structure.

  use Class::MethodMaker
    [ scalar => 'name',
      new    => [qw/ new /],
    ];

The second of the pair may in the most simple case be a single scalar that is
the name of a component to use.

  use Class::MethodMaker
    [ scalar => 'bob', ];

For anything more complex, the second argument must itself be an
arrayreference.  Simple names within this arrayreference are again taken as
component names to use; in the following example, both C<foo> and C<bar>
scalar components are created:

  use Class::MethodMaker
    [ scalar => [qw/ foo bar /], ];

Options to the data-structure, to change the behaviour of the component, or
methods available, etc., are specified by the presence of a hash reference in
line with the component names.  Each key of the hashref is the name of an
option; the corresponding value is the option value.  Option names are easily
recognized by a leading hyphen (C<->) (or leading exclamation mark, C<!>).
The options affect only the components named I<after> the option itself.  In
the following example, C<foo> is non-static (the default), whilst bar is a
static:

  use Class::MethodMaker
    [ scalar => ['foo', { -static => 1 }, 'bar'], ];

Naturally, options may be altered by later settings overriding earlier ones.
The example below has exactly the same effect as the one above:

  use Class::MethodMaker
    [ scalar => [{ -static => 1 }, 'bar', { -static => 0 }, 'foo'], ];

Options that are boolean (on/off) valued, such as C<-static>, may be specified
external to any hashref as C<-optionname> to set them on and C<!optionname> to
set them off.  The example below has exactly the same effect as the one above:

  use Class::MethodMaker
    [ scalar => [ qw/ -static bar !static foo /], ];

Options that take a value, e.g., C<-type>, must be specified within a hashref:

  use Class::MethodMaker
    [ scalar => [ +{ type => 'File::stat' }, 'bob' ], ];

Options affect is limited by the scope of the nearest enclosing arrayref.
This particularly means that for multiple invocations of a data structure
type, options on earlier invocations do not affect later ones.  In the
following example, C<foo> is non-static (the default), whilst bar is a static:

  use Class::MethodMaker
    [ scalar => [ qw/ -static bar /],
      scalar => [ 'foo' ],
    ];

This is true even if later invocations do not use an arrayref.  The example
below has exactly the same effect as the one above:

  use Class::MethodMaker
    [ scalar => [ qw/ -static bar /],
      scalar => 'foo',
    ];

Arrayrefs may be employed within a set of arguments for a single
data-structure to likewise limit scope.  The example below has exactly the
same effect as the one above:

  use Class::MethodMaker
    [ scalar => [ [ qw/ -static bar / ], 'foo' ],
    ];

=head2 Method Renaming

Methods may be renamed, by providing options that map from one generic name to
another.  These are identified by the presence of a '*' in the option name.

The example below installs component C<a> as a scalar, but the method that
would normally be installed as C<a_get> is instead installed as C<get_a>, and
likewise C<set_a> is installed in place of C<a_set>.

  use Class::MethodMaker
    [ scalar => [ { '*_get' => 'get_*',
                    '*_set' => 'set_*', },
                  'a' ],
    ];

=head2 Default & Optional Methods

Class::MethodMaker installs a number of methods by default.  Some methods,
considered to be useful only to a subset of developers are installed only on
request.  Each method is marked in the text to state whether it is installed
by default or only upon request.

To request that a non-default method is installed, one needs to rename it
(even possibly to its normal name).  So, to install the C<*_get> method for a
scalar attribute (as C<*_get>), the syntax is:

  package MyClass;
  use Class::MethodMaker
    [ scalar => [{'*_get' => '*_get'}, 'a'] ];

The method may be installed using a non-default name using similar syntax:

  package MyClass;
  use Class::MethodMaker
    [ scalar => [{'*_get' => 'get_*'}, 'a'] ];

The client may choose to not install a default method by renaming it to undef:

  use Class::MethodMaker
    [ scalar => [{'*' => undef }, 'a'] ];

Note Class::MethodMaker will not install a method in place of an existing
method, so if the intent is to not install a default method because the client
has their own version, an alternative to the above is to define the client
version before calling Class::MethodMaker.

=head2 Naming & Method-Design Conventions

The standard method names are designed with predictability and class
extendibility in mind.

=head3 Naming

For any component I<x> that Class::MethodMaker creates, the method names are
always C<x> or C<x_*>.  This enables predictability, for you do not need to
remember which methods are named C<x_*> and which C<*_x>, and also you can
name methods that you create by avoiding prefixing them with C<x>, and so
avoid any clash with Class::MethodMaker-generated methods (even if
Class::MethodMaker is upgraded with shiny new extra methods).
Class::MethodMaker users may rename methods (see L<Method Renaming>).

For any B<data-structure> component (scalar, array, hash, etc.) I<x> that
Class::MethodMaker creates, the method C<x> I<sets> the value of that
component: i.e., overriding any existing value, not amending or modifying.
E.g., for array components, C<x> does not push or pull values but all old
values are removed, and new ones placed in their stead:

  package MyClass;
  use Class::MethodMaker
    [ array => 'a',
      new   => 'new',
    ];

  package main;
  my $m = MyClass->new;
  $m->a(4,5);
  print join(' ', $m->a), "\n"; # 4 5
  $m->a(6,7);
  print join(' ', $m->a), "\n"; # 6 7

The method returns the I<new> value of the component:

  print join(' ', $m->a(8,9)), "\n"; # 8 9

Note that calling the method with an empty list B<does not> reset the value to
empty; this is so that normal lookups work on the method (i.e., if

  $m->a

emptied the component, then

  @a = $m->a

would always give an empty list: not that useful.

=head3 Set/Unset

Each data-structure component has the concept of being set/unset as a whole,
independent of individual members being set.  Each component starts life unset
(unless a default or default option or tie class has been supplied), and is
becomes set by any assignment.  The component is then reset with the
C<*_reset> method.  Thus it is possible to distinguish between a component
that has been set to an explicitly empty value, and one that has not been set
(or been reset).  This distinction is analogous to the distinction in hashes
between a missing key and a key whose value is undef.

  package MyClass;
  use Class::MethodMaker
    [ new    => 'new',
      scalar => 'x',
    ];

  package main;
  my $m = MyClass->new;

  $\ = "\n";
  print $m->x_isset ? "true" : "false";    # false; components start this way

  my $x = $m->x;
  print defined $n ? "->$n<-" : '*undef*'; # *undef*
  print $m->x_isset ? "true" : "false";    # false; reading doesn't set

  $m->x(undef);
  $x = $m->x;
  print $m->x_isset ? "true" : "false";    # true;
  print defined $n ? "->$n<-" : '*undef*'; # ->foo<-

  $m->x("foo");
  $x = $m->x;
  print $m->x_isset ? "true" : "false";    # true; undef is valid value
  print defined $n ? "->$n<-" : '*undef*'; # *undef*

  $m->x_reset;
  $x = $m->x;
  print defined $n ? "->$n<-" : '*undef*'; # *undef*
  print $m->x_isset ? "true" : "false";    # false

It is not an error to query the value of an unset component: the value is
undef.  Querying (any passive command, or pure function) an unset component
does not cause it to become set; only assigning (any active command, or
procedure) changes the set status of a component.

NOTE THAT lvalues are still experimental (as of perl 5.8.0), and so their
implementation may change r disappear in the future.  Note that lvalue use
defeats type-checking.  This may be considered a bug, and so may be fixed if
possible at some point in the future.

=head3 Other Design Considerations

Further design goals for Class::MethodMaker version 2:

=over 4

=item Consistency of Options

The options passed to components are now handled in a single place, to try to
be phrased consistently.  As many options as possible are common to all
data-structures.

=item Flexibility

It is intended that all common class-construction options are supported across
all data-types, so that e.g., defaults, ties, typing may be used with your
data-structure of choice, and combined.

=item Speed

The methods are intended to be as fast as possible, within other constraints
outlined here.

=back

=head2 Options to C<use>/C<import>

=over 4

=item C<-target_class>

By default, the target class is determined to be the last (latest) class in
the call stack that is not a Class::MethodMaker::Engine subtype.  This is what
is wanted 99% of the time, and typical users need not worry.  However, the
target class may be set explicitly in the call to C<use>/C<import>:

  use Class::MethodMaker
    [ -target_class => 'X',
      scalar        => [qw/ a /],
      -target_class => 'Y',
      scalar        => [qw/ b /],
    ];

Note that the C<-target_class> option is order sensitive: it affects only
components requested I<after> it in the call to C<use>/C<import>.  As shown,
the same call may handle specify multiple target classes.  Any components
requested before the first C<-target_class> are created in the
default-determined class, as outlined above.

Setting the target class in this way does B<not> persist over multiple calls
to C<use>/C<import>.  A subsequent call to either will use the
default-determined class as target (unless again overridden by
C<-target_class>).

=back

=head2 Standard Options for Data-Structure Components.

The following options are observed by all data structure components
(L<scalar|Class::MethodMaker::scalar>, L<array|Class::MethodMaker::array>,
L<hash|Class::MethodMaker::hash>).

=over 4

=item -static

  package MyClass;
  use Class::MethodMaker
    [ scalar => [qw/ -static s /], ];

This option causes components to hold class-specific, rather than
instance-specific values.  Thus:

  package main;
  my $m = MyClass->new;
  my $n = MyClass->new;
  $m->a(4,5);
  print join(' ', $m->a), "\n"; # 4 5
  print join(' ', $n->a), "\n"; # 4 5
  $n->a(6,7);
  print join(' ', $n->a), "\n"; # 6 7
  print join(' ', $m->a), "\n"; # 6 7

=item -type

  use Class::MethodMaker
    [ scalar => [{ -type => 'File::stat' }, 'st' ]];

Takes the name of a class, and checks that all values assigned to the
component are of the appropriate type (uses UNIVERSAL::isa, so subtypes are
permissible).

=item -forward

This option takes as value an arrayref (or a simple scalar).  The values
specify a list of methods that when called on an instance of the target class,
are "forwarded on" to the given component.  For example,

  package X;

  use Class::MethodMaker
    [scalar => [{ -type => 'File::stat',
                  -forward => [qw/ mode size /], },
                'st1',
               ],
    ])},

any call of C<mode> or C<size> on an instance of C<X> will simply call the
method of the same name on the value stored in the component C<st1>, with the
same arguments, and returns the value(s) of this call.

Forwarding only applies to the first named component (since the methodname is
fixed, without the a componentname part).  This is because the components are
installed in the order in which they are created, and Class::MethodMaker never
overwrites a pre-existing method.  So, in the following example, C<mode> and
C<size> forward to the C<st1> component, and C<read> forwards to the C<st2>
component.

  package MyClass;
  Class::MethodMaker->import([scalar =>
                                [{ -type    => 'File::stat',
                                   -forward => [qw/ mode
                                                    size /],
                                 },
                                 qw( st1 ),
                                 { -type    => 'IO::Handle',
                                   -forward => 'read', },
                                 qw( st2 ),
                                ]])},

Forwarding a method to a component of composite data type (e.g., array, hash)
causes the method to be mapped over the values of that component.  The
returned value is appropriate to the component type; so a method forwarded to
an array will return a list, like the array that is the component, but with
each value being the instead result of applying the forwarded method to the
corresponding value of the array.

The following code populates the C<@sizes> array with the sizes of
F</etc/passwd>, F</etc/group>, in that order.

  package main;
  my $m = MyClass->new;
  $m->st1("/etc/passwd", "/etc/group");
  my @sizes = $m->size;

Calling the forwarding method in a scalar context will get the same results,
but as an arrayref:

  my $sizes = $m->size; # [ 921, 598 ] for example

Likewise, forwarding to a hash component will return a hash from original key
to result of method on the corresponding component, or an equivalent hashref
in scalar context.

=item -default

  use Class::MethodMaker
    [ scalar => [{ -default => 7 }, 'df1' ]];

Takes a simple value; must be either undef or an instance of the appropriate
type if C<-type> has also been specified.  Whenever a component is new or
reset, its value(s) default to the value given.  Hence C<*_isset> will always
return true for that component.  For compound data-structures, the default
applies to the each element of the structure, not the compound itself.  So,
for array structures, the default applies to each element of the array, not
the array itself.

It is an error to specify the C<-default> option and the C<-default_ctor>
option simultaneously.

=item -default_ctor

  use Class::MethodMaker
    [scalar => [{ -default_ctor => sub {
                    Y->new(-3);
                  },
                'df2',

                { -type         => 'Y',
                  -default_ctor => 'new' },
                'df3',
               ]
    ];

Takes a coderef to call to generate the default value.  This is called the
first time a value is required, and afterwards whenever reset is called.  The
subr is called with one argument, which is the object upon which the component
exists (or the name of the class upon which the component is created, if the
call is made on the class).

If the C<-type> option is in effect, then the value may be a simple value,
which shall be considered the name of a method to call on the class specified
by C<-type>.

It is an error to specify the C<-default> option and the C<-default_ctor>
option simultaneously.

=cut

Beware when using a default_ctor with lvalue methods; given a statement such
as

  $x->df2_index(2) = Y->new;

where df2 is an array component, assuming index(2) is currently unset, then
index(2) will get a shiny new instance of Y (or whatever the default_ctor
creates), I<before> the assignment takes place --- so there'll be I<2> new
instances created.  In the lvalue case, the component has no way of knowing
whether there'll be an assignment, since it takes place after the call has
completed.

=pod

=item -tie_class

  # @z is an audit trail
  my @z;
  package W;
  use Tie::Scalar;
  use base qw( Tie::StdScalar );
  sub TIESCALAR { push @z, [ 'TIESCALAR'     ]; $_[0]->SUPER::TIESCALAR    }
  sub FETCH     { push @z, [ 'FETCH'         ]; $_[0]->SUPER::FETCH        }
  sub STORE     { push @z, [ STORE => $_[1]  ]; $_[0]->SUPER::STORE($_[1]) }
  sub DESTROY   { push @z, [ 'DESTROY'       ]; $_[0]->SUPER::DESTROY      }
  sub UNTIE     { push @z, [ UNTIE => $_[1]  ]; $_[0]->SUPER::UNTIE($_[1]) }

  package X;
  Class::MethodMaker->import([scalar =>
                                [{ -type      => 'File::stat',
                                   -tie_class => 'W',
                                   -forward   => [qw/ mode
                                                      size /],
                                 },
                                 qw( tie1 ),
                              new => 'new',
                             ]]);

This option takes a simple value as argument, which is taken be the name of a
class that is to be tied to the storage for the component, e.g., for an array
component, a class that implements the API for tied arrays is needed (see
L<Tie::Array> for more information on this).  Likewise for scalar components,
hash components, etc.  Note that it is the component that is tied, not the
data items.

  package main;
  my $x = X->new;

  # @z is empty

  my $stat1 = stat "/etc/passwd";
  my $stat2 = stat "/etc/group";
  $x->tie1($stat1);

  # @z is (['TIESCALAR'], ['STORE', $stat1])

  my $y = $x->tie1;

  # $y is $stat1
  # @z is (['TIESCALAR'], ['STORE', $stat1], ['FETCH'])

  $x->tie1($stat2);

  # @z is (['TIESCALAR'], ['STORE', $stat1], ['FETCH'], ['STORE', $stat2])

  $x->tie1_reset;

  # @z is (['TIESCALAR'], ['STORE', $stat1], ['FETCH'], ['STORE', $stat2],\
  #        ['DESTROY'])

=cut

Note that using a tied component will render the use of lvalue subs
unsupported for that component.

=pod

=item -tie_args

  package X;
  Class::MethodMaker->import
    ([scalar => [{ -tie_class => 'V',
                   -tie_args  => [enum    => [qw/A B C/],
                                  default => 'B'],
                 },
                 qw( tie2 ),
                ]]);

This option takes an array reference, whose members are passed as arguments to
any tie invoked on the component (by virtue C<-tie_class>).  If C<-tie_class>
is not in force, this is ignored.

As a convenience measure, a single argument may be passed directly, rather
than embedding in an array ref --- unless that arg is an array ref itself...

=item -read_cb

B<The implementation of this option is incomplete>

  package MyClass;
  use Class::MethodMaker
    [ scalar => [{ -read_cb => sub { ($_[1]||0) + 1 } }, 'rcb1' ]
      new    => 'new';
    ];

This option takes as argument a coderef, which is called whenever a value is
read.  It is called with two arguments: the instance upon which the method was
called, and the value stored in the component.  The return value of the given
coderef is the value which is passed to the caller of the method as the
component value.  Thus, the above example adds one to whatever the stored
value is.  Note that the value is returned to the callee, but not stored in
the object

  package main;
  my $m = MyClass->new;
  $m->rcb1(4);
  my $n = $x->rcb1; # 5
  my $n = $x->rcb1; # 5

=item -store_cb

B<The implementation of this option is incomplete>

  package MyClass;
  use Class::MethodMaker
    [ scalar => [{ -store_cb => sub { $_[1] + 1 } }, 'scb1' ]
      new    => 'new';
    ];

This option takes as argument a coderef, which is called whenever a value is
stored.  It is called with four arguments: the instance upon which the method
was called, the value to store in the component, the name of the component,
and the previous value of the component (if any; if the given element of the
component was previously unset, only three arguments are passed).

The return value of the given coderef is the value which is actually stored in
the component.  Thus, the above example stores 1 greater than the value passed
in.

  package main;
  my $m = MyClass->new;
  $m->scb1(4);
  my $n = $x->scb1; # 5

Generally, store callbacks are cheaper than read callbacks, because values are
read more often than they are stored.  But that is a generalization.  YMMV.

=back

=head1 EXPERIMENTAL & COMPATIBILITY notes

Some new facilities may be marked as EXPERIMENTAL in the documentation.
These facilities are being trialled, and whilst it is hoped that they
will become mainstream code, no promises are made.  They may change or
disappear at any time.  Caveat Emptor.  The maintainer would be
delighted to hear any feedback particularly regarding such facilities,
be it good or bad, so long as it is constructive.

Some old facilities may be marked as COMPATIBILITY in the documentation.
These facilities are being maintained purely for compatibility with old
versions of this module, but will ultimately disappear.  They are normally
replaced by alternatives that are considered preferable.  Please avoid using
them, and consider amending any existing code that does use them not to.  If
you believe that their removal will cast an unacceptable pall over your life,
please contact the maintainer.

=head1 SEE ALSO

L<Class::MethodMaker::Engine>, L<Class::MethodMaker::scalar>,
L<Class::MethodMaker::array>, L<Class::MethodMaker::hash>,
L<Class::MethodMaker::V1Compat>

=cut

