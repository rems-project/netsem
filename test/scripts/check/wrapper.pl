#!/usr/bin/perl -w
#
# wrapper for running HOL stuff
#

# POSIX::nice exists, but there's no standard setrlimit(); BSD::Resource
# isn't standard...  :-( :-(  Hence this nasty two-stage wrapper.


use strict;
use Getopt::Std;

my @INUSEARGS=("--client=tthee");
my @DURARGS=("--duration=1800");
my $DEBUG=0;
my $SUSPEND=1;  # should client be suspended or killed when machine becomes inuse?

# autoflush
$| = 1;

# read in-use script name, if present:
my @INUSESCRIPT = ();
if ($ARGV[0] eq "-i") {
    shift @ARGV;
    @INUSESCRIPT = (shift @ARGV);
} elsif ($ARGV[0] =~ /^-i(.*)$/) {
    @INUSESCRIPT = $1;
    shift @ARGV;
}

if (@INUSESCRIPT == 0) {
    # If no inuse script, no need to do inuse thing; just exec()
    $DEBUG && print "No in-use script specified; handing over control to compute job.\n";
    exec @ARGV;
    die "Exec failed: $!\n";
}

my @INUSE = (@INUSESCRIPT,@INUSEARGS);

# set up a signal handler to kill them if we are killed
my $COMPUTEPID;
my $INUSEPID;
$SIG{INT} = \&handle_signal;
$SIG{TERM} = \&handle_signal;

my $exitstatus = 63;
my $status;

if (!(system(@INUSE,@DURARGS) >> 8)) {
    print "\nINUSE KILL: Not starting; machine is in use\n";
} else {
    $DEBUG && print "Start compute job\n";
    $COMPUTEPID = forkoff(@ARGV);
    $DEBUG && print "$COMPUTEPID\n";
    while (1) {
        $DEBUG && print "Start in-use job\n";
        $INUSEPID = forkoff(@INUSE,"--wait=busy");
        $DEBUG && print "$INUSEPID\n";

        $DEBUG && print "Wait...\n";
        my $pid = wait();
        $status = $?;
        $DEBUG && print "got $pid\n";
        if ($pid == $COMPUTEPID) {
            # It is tempting to put some notification message here for the driver script
            # to let it know that the job has complete.  But we should not do this.
            # If there is no inuse script, then none of this code is used - the compute job
            # is executed on its own.  So if the driver script depended on such messages,
            # it would be broken.
            printf("\nNormal completion of compute job: job %s.\n",strstatus($status));
            $exitstatus = $status>>8;
            kill 'TERM', $INUSEPID;
            waitpid($INUSEPID,0);
            last;  # break out of inuse loop
        } elsif ($pid == $INUSEPID) {
            if ($SUSPEND) {
                kill 'STOP', $COMPUTEPID
                    or printf("Weird: got error from SIGSTOP: $!\n");
                print "\nINUSE STOP: Job stopped; waiting until machine becomes idle.\n";
                $status = system(@INUSE,@DURARGS,"--wait=idle");
                printf("\nINUSE CONT: Machine idle: inuse %s. Job continuing.\n",strstatus($status));
                kill 'CONT', $COMPUTEPID
                    or printf("Weird: got error from SIGCONT: $!\n");
            } else {
                printf("\nINUSE KILL: Killing compute job; machine is in use: inuse %s.\n",strstatus($status));
                $exitstatus = 62;
                kill 'TERM', $COMPUTEPID;
                waitpid($COMPUTEPID,0);
                last;  # break out of inuse loop
            }
        } else {
            printf("Weird: got pid $pid from wait(): %s\n",strstatus($status));
            last;  # break out of inuse loop
        }
    } continue {
        sleep 5;  # avoid nasty tight loops if @INUSE fails for some reason
    }
}

print "\nINUSE WAIT: Waiting until machine is idle before yielding control.\n";
$status = system(@INUSE,@DURARGS,"--wait=idle");
printf("Machine idle: inuse %s.  Completing.\n",strstatus($status));

exit($exitstatus);

sub forkoff {
    my @prog = @_;
    my $pid = fork();
    if (defined($pid) && $pid==0) {
        # we are child
        $DEBUG && print ("Execing ".join(" ",@prog)."...\n");
        exec(@prog);
        die ("Exec of ".join(" ",@prog)."failed: $!\n");
    }
    # we are parent; return pid
    $_ = $pid;
}

sub handle_signal {
    my $thesig = shift;

    foreach my $pid ($COMPUTEPID, $INUSEPID) {
        kill $thesig => $pid if defined($pid);
        kill 'CONT'  => $pid if defined($pid);  # in case it's stopped
    }

    die "$0: Cleaned up processes on SIG$thesig.  Exiting now.\n";
}

sub strstatus {
    my ($status) = @_;
    my $exitcode = $status>>8;
    my $coredump = $status&128;
    my $signal = $status&127;
    sprintf("exit(%d)%s%s",$exitcode,
            $signal ? sprintf(" on signal %d",$signal) : "",
            $coredump ? ", dumped core" : "");
}

