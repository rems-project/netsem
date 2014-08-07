#! /usr/bin/perl -w
# inuse2.pl; option handling based on PB's inuse.pl
# $Id: inuse2.pl,v 1.5 2004/04/02 09:59:17 kw217 Exp $
# Use "pod2text" for info

=head1 NAME

inuse2 -- determine whether the machine is in use, or available for others

=head1 SYNOPSIS

inuse [--wait=[busy|idle]] [--duration=<seconds>] [--client=<clientname>] [--sleep=<seconds>] [--verbose] [--help]

=head1 OPTIONS

=over 4

=item B<--wait=[busy|idle]>

Do not return until the machine is B<busy> or B<idle>.

=item B<--duration=>I<seconds>

The job is likely to last I<seconds> seconds,
so check whether the machine is likely to be free is
I<seconds> as well, e.g. is there a booking such as a practical.

=item B<--client=>I<clientname>

The client is I<clientname>.
This may be effect the policy about when it should run.

=item B<--sleep=>I<seconds>

Sleep I<seconds> between testing when using B<--wait>.

=item B<--verbose>

generate comments as to what it is doing.

=item B<--help>

generate help info.

=back

=head1 DESCRIPTION

Script to test whether a machine is in use.

It takes account of the allowed and denied periods detailed in
the file F</usr/groups/tthee/conf/>I<machinename.domain>.

The above-named file contains lines of the form

=over

=item B<tz> I<timezone-specifier>

=item B<allow> I<timespec>

=item B<deny> I<timespec>

=back

# comments are also allowed, and blank lines.

Initially computation is allowed at all times.  The file is then read
sequentially, with each line specifying an interval or set of
intervals during which execution is allowed or denied.  Later lines
override earlier ones.

Times are specified by default in Coordinated Universal Time (UTC).
The timezone used may be changed by giving a I<timezone-specifier>, in
the same format as used for the B<TZ> environment variable (see
L<tzset(3)>).  For example:

=over

=item B<tz :Europe/London>

=back

specifies British time (GMT in winter, BST in summer).  See
F</usr/share/zoneinfo/> for the supported timezones.  The B<tz>
declaration must come before any B<allow> or B<deny> lines.

A I<timespec> is given in the same format as in L<crontab(5)>: there
are five whitespace-separated fields, each of which may be B<*>
(wildcard) or a comma-separated list of one or more numbers or ranges.
The fields are as follows:

       field          allowed values
       -----          --------------
       minute         0-59
       hour           0-23
       day of month   1-31
       month          1-12
       day of week    0-7 (0 or 7 is Sun)

A field may be an asterisk (*), which always stands for
``first-last''.

Ranges of numbers are allowed.  Ranges are two numbers separated with
a hyphen.  The specified range is inclusive.  For example, 8-11 for an
``hours'' entry specifies execution at hours 8, 9, 10 and 11.

Lists are allowed.  A list is a set of numbers (or ranges) separated
by commas.  Examples: ``1,2,5,9'', ``0-4,8-12''.

Step values and names (see L<crontab(5)>) are not supported.

For example,

    tz :Europe/London
    deny * 8-17 * * *
    allow * * * * 0,6

specifies use outside British working hours on weekdays, and at all
times on weekends.

The file is polled every sleep interval (60 seconds by default).

If there is a syntax error, the file owner will be emailed.  This
should happen at most once per file change, as regulated by
F</usr/groups/tthee/conf/.emailed.>I<machinename.domain>.

=cut

use strict;
use Getopt::Long;
use Pod::Usage;
use Sys::Hostname;
use POSIX;

my $CONFDIR = "/usr/groups/tthee/conf";
my $EMAILLOGPREFIX = ".emailed.";

my $SENDMAIL = "/usr/lib/sendmail";
my $MAILER   = "Keith's hand-crafted Perl mailer v2.3 [2004-03-30]";
my $FAKESEND = 0;

my @RSHPASSWDHOST = ("/usr/bin/ssh","shep");

my $wait;
my $duration	= 0;
my $client	= "UnKnown";
my $waitfor	= 0;
my $sleep	= 60;
my $help;
my $verbose	= 0;
my %opts = (
	"wait=s"	=> \$wait,
	"client=s"	=> \$client,
	"duration=i"	=> \$duration,
	"sleep=i"	=> \$sleep,
	"verbose"	=> \$verbose,
	"help"		=> \$help,
);

my @ORIG_ARGV = @ARGV;

GetOptions (%opts) || pod2usage();
pod2usage(-verbose => 2) if $help;
# Decode the "--wait" value
if (defined($wait)) {
	if ($wait =~ /^busy$/i) { $waitfor = 1; }
	elsif ($wait =~ /^idle$/i) { $waitfor = -1; }
	else { pod2usage(); }
}
pod2usage() if $sleep < 1;

# set up config file
my $hostname = hostname;
my $configfile = "$CONFDIR/$hostname";
my $emaillogfile = "$CONFDIR/$EMAILLOGPREFIX$hostname";
my $config;  # the current configuration
my $lastconfigdate = 0;
my $configfilevalid = 0;

# has TZ been set already?  (it is cached in libc, so we can set it only once per process)
#  (and if so, to what?)
my $TZ;

# See whether in use for the requested duration.
my($inuse, $interval) = &inuse(time, $duration);

# If no wait, give the answer immediately
exit(&exitcode($inuse)) unless $waitfor;
# If waiting for a busy period and it is busy for the duration, answer
exit(&exitcode($inuse)) if $waitfor > 0 && $inuse;
# If waiting for an idle period and it is idle for the duration, answer
exit(&exitcode($inuse)) if $waitfor < 0 && ! $inuse;

# OK - told to wait.
# If &inuse gave us a duration to sleep, do so.
if ($interval) {
	print STDERR "::: inuse(time, $duration) suggested sleep $interval\n" if $verbose;
	sleep($interval);
}

# if waiting for busy, ignore the duration ?
# $duration = 0 if $waitfor > 0;

while (sleep($sleep)) {
	my($inuse, $interval) = &inuse(time, $duration);
	exit(&exitcode($inuse)) if $waitfor > 0 && $inuse;
	exit(&exitcode($inuse)) if $waitfor < 0 && ! $inuse;
}

# Is the machine in use (at any point) from $when to $when+$duration ?
# TODO: DURATION HANDLING UNIMPLEMENTED!!
# Returns boolean and when to try again.
sub inuse {
	my($when, $duration) = @_;

        $verbose && print STDERR "inuse($when,$duration) = ";
        rereadconfig();
        my ($inuse,$interval);
        if ($configfilevalid) {
            ($inuse,$interval) = (!allowed($when,$config),1);
        } else {
            # no config file; safely assume in use
            ($inuse,$interval) = (1,1);
        }
        $verbose && print STDERR "($inuse,$interval)\n";
        return ($inuse,$interval);
}

sub exitcode {
	my($rc) = @_;
	return !$rc;
}

sub allowed {
    my ($when, $theconfig) = @_;

    my $intervals = $theconfig->{'intervals'};

    if (!defined($TZ)) {
        $TZ = $theconfig->{'zone'};
        $ENV{'TZ'} = $TZ;
    } elsif ($theconfig->{'zone'} ne $TZ) {
        $verbose && print STDERR "Timezone change ('$TZ' -> '$theconfig->{'zone'}').  Restarting.\n";
        exec $0 ($0,@ORIG_ARGV)
             or print STDERR "exec() failed: $!\n";
        exit(&exitcode(1));  # say we're in use; that's safe.  Hopefully we'll be called again.
    }

    my @time = (localtime($when))[1,2,3,4,6];
    $time[3]++;  # month 1..12

    my $allowed = 1;
    foreach my $spec (@$intervals) {
        my $inspec = 1;
        for (my $i = 0; $i < 5; $i++) {
            $inspec &&= $spec->[$i+1]->[$time[$i]];
        }
        if ($spec->[0]) {
            $allowed ||= $inspec;
        } else {
            $allowed &&= !$inspec;
        }
    }

    return $allowed;
}


sub parsespec {
    my ($line,$s,$min,$max) = @_;

    my @vect;
    if ($s eq "*") {
        @vect = (1) x ($max+1);
    } else {
        @vect = (0) x ($max+1);
        die "Bad specifier $s in configuration line $.: $line\n"
            unless ($s =~ /^[0-9]+(?:-[0-9]+)?(?:,[0-9]+(?:-[0-9]+)?)*$/);
        while ($s =~ /([0-9]+)(?:-([0-9]+))?/g) {
            if (defined($2)) {
                die "Out-of-range specifier $s in configuration line $.: $line\n"
                    if $1 < $min || $1 > $max || $2 < $min || $2 > $max;
                splice(@vect,$1,$2-$1+1,(1)x($2-$1+1));
            } else {
                die "Out-of-range specifier $s in configuration line $.: $line\n"
                    if $1 < $min || $1 > $max;
                $vect[$1] = 1;
            }
        }
    }
    return \@vect;
}

sub readconfig {

    my @intervals = ();

    $verbose && print STDERR "Reading config file $configfile...";

    my $zone = ":UTC";  # default

    open CFG, "<$configfile"
        or die "Couldn't open config file $configfile for reading: $!\n";

    my $tzOK = 1;
    while (<CFG>) {
        chomp;
        s/^\s+//;
        s/\s+$//;
        next if /^\#/;
        next if /^$/;

        if (/^(allow|deny)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)$/i) {
            my $allow = (lc($1) eq "allow");
            my @spec = ($allow,
                        parsespec($_,$2,0,59),
                        parsespec($_,$3,0,23),
                        parsespec($_,$4,1,31),
                        parsespec($_,$5,1,12),
                        parsespec($_,$6,0,7));
            push @intervals, \@spec;
            $tzOK = 0;
        } elsif (/^tz\s+(.*)$/i) {
            if ($tzOK) {
                $zone = $1;
                $tzOK = 0;
            } else {
                die ("tz declaration must occur before allow or deny, and must not be duplicated.\n" .
                     "On configuration line $.: $_\n");
            }
        } else {
            die "Invalid configuration line $.: $_\n";
        }
    }

    close CFG
        or die "Couldn't close config file $configfile for reading: $!\n";

    $verbose && print STDERR "...done\n";

    $config = { 'intervals' => \@intervals,
                'zone'      => $zone };
}

sub rereadconfig {
    my ($uid,$thisconfigdate) = (stat $configfile)[4,9];
    if (!defined($uid)) {
        $lastconfigdate = 0;
        $configfilevalid = 0;
        print STDERR "Config file missing!  Assuming always inuse.\n";
        return;
    }
    if ($thisconfigdate == $lastconfigdate) {
        return;
    } else {
        $lastconfigdate = $thisconfigdate;
        $configfilevalid = 0;
        eval {
            readconfig();
            $configfilevalid = 1;
        };
        if ($@ && $thisconfigdate != lastconfigemail()) {
            my $owner = bettergetpwuid($uid);
            notifyerr($owner,$@);
            logconfigemail($thisconfigdate);
        }
    }
}

# getpwuid doesn't work if the user doesn't have an entry on this
# machine's passwd file

sub bettergetpwuid {
    my ($uid) = @_;
    my $name = scalar(getpwuid($uid));
    if (!defined($name)) {
        $verbose && print STDERR "Looking up UID $uid remotely.\n";
        open NAME, "-|", (@RSHPASSWDHOST,"perl","-e","'print scalar(getpwuid($uid))'")
            or die "Problems opening pipe: $!\n";
        $name = <NAME>;
        chomp $name;
        close NAME
            or die "Problems closing pipe: $!\n";
    }
    return $name;
}

sub logconfigemail {
    my ($thisconfigdate) = @_;

    open OUT, ">$emaillogfile"
        or die "Couldn't open email logfile $emaillogfile for output: $!\n";
    print OUT "$thisconfigdate\n";
    close OUT
        or die "Couldn't close email logfile $emaillogfile for output: $!\n";
    chmod 0660, $emaillogfile
        or warn "Couldn't chmod email logfile $emaillogfile: $!\n";
}

sub lastconfigemail {
    if (open IN, "<$emaillogfile") {
        $_ = <IN>;
        chomp $_;
        close IN
            or die "Couldn't close email logfile $emaillogfile for input: $!\n";
    } else {
        $_ = "0";
    }
    return $_;
}

sub notifyerr {
    my ($owner,$err) = @_;

    my $body = <<EOF;
Hi $owner,

Your configuration file $configfile has an error:

$err

Please correct it at your convenience.  The file will be rescanned
shortly after you modify it, or as soon as a check run is started if
there is not one currently in progress.  As long as this syntax error
remains, your machine $hostname will not be used for checking.

You should receive this email only once.  In the event of difficulty,
please contact Keith Wansbrough <kw217\@cl.cam.ac.uk>

-- The Netsem Team.
EOF

    sendmsg("Syntax error: $configfile",
            "The Netsem Team <kw217\@cl.cam.ac.uk>",
            $owner,
            [$owner,"kw217\@cl.cam.ac.uk"],
            $body,
            "X-netsem: syntax error");
}

# send an email
sub sendmsg {
    my ($subject,$from,$to,$addrs,$body,$extraheaders) = @_;
    my @addrs = @$addrs;
    die "Missing argument to sendmsg"
        unless defined($subject) && defined($from) && defined($to) && defined($body);

    # because there are localtime calls here, better make sure we log the TZ caching.
    if (!defined($TZ)) {
        if (defined($ENV{'TZ'})) {
            $TZ = $ENV{'TZ'};
        } else {
            $TZ = ":UTC";
        }
        $ENV{'TZ'} = $TZ;
    }

    my $datestamp = POSIX::strftime("%a %b %e %T %Y",localtime($^T));
    my $fulldatestamp = POSIX::strftime("%a, %d %b %Y %T %z",localtime($^T));

    if (!defined($extraheaders)) {
        $extraheaders = "";
    };
    if ($extraheaders ne "" && !($extraheaders =~ /\n$/)) {
        $extraheaders .= "\n";
    }

    my $themsg = <<"EOF";
From: $from
To: $to
Date: $fulldatestamp
Subject: $subject
MIME-Version: 1.0
Content-Type: text/plain; charset=\"iso-8859-1\"
Content-Transfer-Encoding: 8bit
${extraheaders}X-Mailer: $MAILER

$body
EOF

    if (!($themsg =~ /\n$/)) {
        $themsg .= "\n";
    }

    my ($pid);

    if ($FAKESEND) {
        $verbose && print STDERR ("Faking (not performing) send to " . scalar(@addrs) . " recipients! (" . join(",",@addrs) . ")\n");
    } else {
        $verbose && print STDERR "Sending...";
        $pid = open SENDMAIL, "|-";
        if (defined($pid)) {
            if ($pid==0) {
                # child
                system($SENDMAIL,"-oi",@addrs)==0
                    or die "Error executing mailer ($SENDMAIL): $!\n";
                exit 0;
            } else {
                # parent
                print SENDMAIL $themsg;
                close SENDMAIL
                    or die "Error closing mailer pipe: $!\n";
                waitpid($pid,0);
            }
        } else {
            die "Couldn't open pipe: $!\n";
        }
        $verbose && print STDERR ("sent to " . scalar(@addrs) . " recipients! (" . join(",",@addrs) . ")\n");
    }
}


