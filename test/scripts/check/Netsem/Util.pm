package Netsem::Util;

require 5.004;

require Exporter;
@ISA = qw(Exporter);
@EXPORT = qw(relpath);
@EXPORT_OK = qw();

use Carp;
use strict;

use vars qw($VERSION);

$VERSION = 2004.0325;

# ----------------------------------------------------------------------

# compute relative path

sub relpath {
    my ($here,$there) = @_;

    $here =~ s{//+}{/}g;
    $there =~ s{//+}{/}g;

    if (! ($here =~ s{^/}{} && $there =~ s{^/}{})) {
        # warn "Can't compute relative path of relative paths:\n  $here\n  $there\n";
        return "/BOGUS_PATH/$there";
    }

    my $relpath = "";

    for (;;) {
        my $h = $here;
        last if !($h =~ s{(^[^/]+)/}{});
        my $hi = $1;
        my $t = $there;
        last if !($t =~ s{(^[^/]+)/}{});
        my $ti = $1;
        last if $hi ne $ti;
        $here = $h;
        $there = $t;
    }

    my @foo = ($here =~ m{/}g);
    my $up = scalar(@foo);
    return ("../" x $up) . $there;
}

# ----------------------------------------------------------------------

1;
