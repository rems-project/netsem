package Netsem::AnnotsParse;

require 5.004;

require Exporter;
@ISA = qw(Exporter);
@EXPORT = qw(&readannots);
@EXPORT_OK = qw();

use Carp;
use strict;

use vars qw($VERSION);

$VERSION = do { my @r = (q$Revision: 1.1 $ =~ /\d+/g); sprintf "%d."."%03d" x $#r, @r }; # must be all one line, for MakeMaker

# ----------------------------------------------------------------------

# The annotations file is a sequence of blocks, with comments
# interleaved.  Comments are arbitrary.  A block begins with a line
# containing a * in the first column, followed immediately by a "code"
# (with no spaces), then some white space, then a "description" to the
# end of the line.  A block is terminated by a blank line (only
# whitespace).  Each group of four digits in the block is treated as a
# trace number.  Other content is ignored.

sub readannots ($ ) {
    my ($afile) = @_;

    my %ann = ();

    if (open(ANN, "<$afile")) {
        while (<ANN>) {
            next unless /^\*(\S+)\s+(?:([A-Z]+)\s+)?(.*)$/;
            my ($code,$cat,$desc) = ($1,$2,$3);
            while (<ANN>) {
                last if /^\s*$/;
                foreach my $trace (/\d{4}/g) {
                    $ann{"trace$trace"} = { 'code' => $code, 'cat' => $cat, 'desc' => $desc };
                }
            }
            last if !defined($_);
        }
        close ANN
            or die "Error closing annotation file $afile: $!\n";
    }
    return \%ann;
}

# ----------------------------------------------------------------------

1;
