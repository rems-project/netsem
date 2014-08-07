package Netsem::LogParse;

require 5.004;

require Exporter;
@ISA = qw(Exporter);
@EXPORT = qw($time0 $timeL %workers %workerids %jobs %stateorder %sporder $TOTAL $ttrans &genericparselog &parselog &getstarttimes $thetrans %time @notime $mintime $minwkey $maxtime $maxwkey &workercmp &statecmp &spcmp &maxkeylen &gettraceinfo &gettracelengths);
@EXPORT_OK = qw();

use Carp;
use strict;

use vars qw($VERSION);

$VERSION = do { my @r = (q$Revision: 1.17 $ =~ /\d+/g); sprintf "%d."."%03d" x $#r, @r }; # must be all one line, for MakeMaker

# ----------------------------------------------------------------------

# parse a log file from stdin

# arguments:
#
# $logfile is the file to read, or undef to default to <ARGV>.
# $time1 is the time to take as the end of the run, or undef to
#   default to the time of the last event.

# global variables:

our ($time0, $timeL);
our %workers;
our %workerids;
our %jobs;
our %stateorder;
our %sporder;
our $TOTAL;
our $ttrans;
our $thetrans;
our %time;
our @notime;
our ($mintime,$minwkey);
our ($maxtime,$maxwkey);

sub genericparselog {
    my ($logfile,$func,$stepfunc) = @_;

    carp "No logfile specified" unless defined($logfile);
    carp "First function not specified" unless defined($func);
    # second function is optional

    # open file if necessary
    if (defined($logfile)) {
        open IN, "<$logfile"
            or carp "Couldn't open log file $logfile for reading: $!\n";
    }

    # read log
    while (1) {  # can't compute handle, because ARGV is only special in <ARGV>
        if (defined($logfile)) {
            last unless (defined($_ = <IN>));
        } else {
            last unless (defined($_ = <>));
        }
        chomp;
        next unless /^(\[\d+\]: >)?==/;
        if (defined($1)) { # Step label
            next unless /^(\[\d+\]): >==Step/;
            carp "Can't parse line: $_\n" unless /^(\[\d+\]): >==Step\s+(\d+)\s+at\s+<([^>]*)>\s+(\d+):$/;
            my ($workerid,$step,$htime,$time) = ($1,$2,$3,$4);

            # ARGS PASSED TO FUNCTION:
            #
            # $workerid  string  short-form worker ID (e.g., "[42]")
            # $step      number  step number
            # $htime   string   human-readable time
            # $time    number   machine-readable time (seconds since epoch)

            defined($stepfunc) && &$stepfunc($workerid,$step,$htime,$time);

        } else { # State change label
            carp "Can't parse line: $_\n" unless /^==([^-\s]+)(-)?\s+(\S+)\s+\"([^\"]*)\"\s+at\s+<([^>]*)>\s+(\d+)$/;
            my ($state,$asleep,$worker,$job,$htime,$time) = ($1,defined($2),$3,$4,$5,$6);

            # ARGS PASSED TO FUNCTION:
            #
            # $state   string   worker state (e.g., "Processing")
            # $asleep  boolean  is worker currently asleep?
            # $worker  string   worker ID
            # $job     string   job ID
            # $htime   string   human-readable time
            # $time    number   machine-readable time (seconds since epoch)

            &$func($state,$asleep,$worker,$job,$htime,$time);
        }
    }

    # close file if necessary
    if (defined($logfile)) {
        close IN
            or carp "Couldn't close log file $logfile for reading: $!\n";
    }

    return;

}


sub parselog {
    my ($logfile,$time1) = @_;

    my $thestartstate = "Processing";

    #
    # We maintain a big state transition table.
    #
    # $time0 is the time of the first event, set at the beginning.
    # $timeL is the time of the latest event, and ultimately of the last event.
    #
    # %workers is a hash containing info on each worker, indexed by worker
    #   (e.g., "akan.cl.cam.ac.uk[42]").
    # %workerids is a hash mapping shortform workerids (e.g., "[42]")
    #   to workers (e.g., "akan.cl.cam.ac.uk[42]").
    # %$workers{$worker} is a hash containing the info for a particular worker.
    # $workers{$worker}->{'time'} is the time of the latest event for that worker
    # $workers{$worker}->{'state'} is the latest state of that worker (with
    #   "0" for the initial state, and "1" for the final state)
    # $workers{$worker}->{'job'} is the job currently being worked on
    #   (with "" if none)
    # $workers{$worker}->{'awake'} is the latest awakeness flag for
    #   that worker
    # $workers{$worker}->{'timeawake'} is the time spent awake in
    #   the current state so far
    # $workers{$worker}->{'timeasleep'} is the time spent asleep in
    #   the current state so far
    # %$workers{$worker}->{'trans'} is the transition table hash for that worker,
    #   indexed by the transition (e.g., "Starting->Crashed").
    # %$workers{$worker}->{'trans'}->{$tindex} is a hash containing info for a
    #   particular transition
    # $workers{$worker}->{'trans'}->{$tindex}->{'time'} is the total awake time taken
    #   for all instances of this transition
    # $workers{$worker}->{'trans'}->{$tindex}->{'count'} is the number of
    #   instances of this transition (this is never zero).
    #
    # $stateindex starts at zero, and is incremented each time we see a
    #   state for the first time.  It is used in building %stateorder.
    # %stateorder is a hash mapping each state to an index, giving us
    #   a canonical ordering for states.  The order is the order in which
    #   we see the states, with "0" first and "1" last.
    #
    # %jobs is a hash keyed on job names, containing info on each job
    # $jobs{$job}->{'state'} is the most recent state of that job
    # $jobs{$job}->{'start'} is the time of the most recent start on that job
    # $jobs{$job}->{'end'} is the time of the most recent end on that job
    #   (undefined when job is currently running)
    # $jobs{$job}->{'timeawake'} is the awake time expended so far on the
    #   current run of the job
    # $jobs{$job}->{'timeasleep'} is the asleep time expended so far on the
    #   current run of the job
    # $jobs{$job}->{'count'} is the number of starts on that job
    # $jobs{$job}->{'worker'} is the most recent worker for that job
    # $jobs{$job}->{'trunc'} is true if the job was running at time 1, and false otherwise
    # $jobs{$job}->{'curstep'} is the current step being processed
    # $jobs{$job}->{'maxstep'} is the maximum step reached
    # $jobs{$job}->{'nsteps'} is the number of steps attempted, minus
    #   one (i.e., the number of steps completed)

    # read in data into state transition table per worker
    %workers = ();
    %workerids = ();
    my $stateindex = 0;
    %stateorder = ('0', $stateindex++);
    %jobs = ();

    my $callback = sub ($$$$$$ ) {
                        my ($state,$asleep,$worker,$job,$htime,$time) = @_;
                        my $awake = !$asleep;
                        # print "$time: $state ($awake): $worker / $job\n";
                        if (!defined($time0)) {
                            $time0 = $time;  # time of first event
                        }
                        $timeL = $time;  # time of latest event
                        if (!defined($stateorder{$state})) {
                            $stateorder{$state} = $stateindex++;
                        }
                        if (!defined($workers{$worker})) {
                            my ($workerid) = $worker =~ /(\[\d+\])/;
                            $workers{$worker} = {'time' => $time0,
                                                 'state' => '0',
                                                 'job' => '',
                                                 'awake' => 1,
                                                 'timeawake' => 0,
                                                 'timeasleep' => 0,
                                                 'trans' => {}};
                            $workerids{$workerid} = $worker;
                        }
                        my $w = $workers{$worker};
                        my $lasttime = $w->{'time'};
                        my $laststate = $w->{'state'};
                        my $lastawake = $w->{'awake'};
                        $w->{'time'} = $time;
                        $w->{'awake'} = $awake;
                        $w->{'job'} = $job;

                        # record elapsed time
                        my $elapsedtime = $time - $lasttime;
                        if ($lastawake) {
                            $w->{'timeawake'} += $elapsedtime;
                        } else {
                            $w->{'timeasleep'} += $elapsedtime;
                        }

                        # if there's been a state transition, record it
                        if ($state ne $laststate) {

                            # record the transition
                            my $trans = $w->{'trans'};
                            my $tindex = "$laststate->$state";
                            if (!defined($trans->{$tindex})) {
                                $trans->{$tindex} = {'time' => 0,
                                                     'count' => 0 };
                            }
                            $trans->{$tindex}->{'time'} += $w->{'timeawake'};
                            $trans->{$tindex}->{'count'}++;

                            # record the job
                            if ($job ne "") {
                                if (!defined($jobs{$job})) {
                                    $jobs{$job} = {'state' => '0',
                                                   'start' => undef,
                                                   'end' => undef,
                                                   'timeawake' => undef,
                                                   'timeasleep' => undef,
                                                   'count' => 0,
                                                   'worker' => undef,
                                                   'trunc' => '',
                                                   'curstep' => -1,
                                                   'maxstep' => -1,
                                                   'nsteps' => -1,
                                               };
                                }
                                my $j = $jobs{$job};
                                if ($state eq $thestartstate) { # start
                                    $j->{'start'} = $time;
                                    $j->{'end'} = undef;
                                    $j->{'count'}++;
                                    $j->{'worker'} = $worker;
                                    $j->{'curstep'} = -1;
                                    $j->{'maxstep'} = -1;
                                    $j->{'nsteps'} = -1;
                                } elsif ($j->{'state'} eq $thestartstate) { # end
                                    $j->{'end'} = $time;
                                    $j->{'trunc'} = 1 if $state eq '1';
                                    $w->{'job'} = '';  # worker no longer processing job
                                } # else do nothing
                                # always update state and times
                                $j->{'state'} = $state;
                                $j->{'timeawake'} = $w->{'timeawake'};
                                $j->{'timeasleep'} = $w->{'timeasleep'};
                            }

                            # now update the current state ready for the next event
                            $w->{'state'} = $state;
                            $w->{'timeawake'} = 0;
                            $w->{'timeasleep'} = 0;

                        }
                    };

    my $stepcallback = sub ($$$$ ) {
        my ($workerid,$step,$htime,$time) = @_;

        my $job = $jobs{$workers{$workerids{$workerid}}->{'job'}};
        $job->{'curstep'} = $step;
        $job->{'maxstep'} = $step if $step > $job->{'maxstep'};
        $job->{'nsteps'}++;

    };

    genericparselog($logfile,\&$callback,\&$stepcallback);

    # add transition to 1, the final state
    if (!defined($time1)) {
        $time1 = $timeL;  # place it at the time of the most recent event
    }
    foreach my $wkey (keys(%workers)) {
        &$callback('1',0,$wkey,$workers{$wkey}->{'job'},undef,$time1);
    }

    # build state-pair order:
    %sporder = ();
    my $spindex = 0;
    foreach my $fstate (sort statecmp keys(%stateorder)) {
        foreach my $tstate (sort statecmp keys(%stateorder)) {
            $sporder{"$fstate->$tstate"} = $spindex++;
        }
    }

    # add dummy "total" worker:
    $TOTAL='TOTAL';
    $workers{$TOTAL} = { 'time' => 0,
                          'state' => 1,
                          'trans' => {} };
    my $tw = $workers{$TOTAL};
    $ttrans = $tw->{'trans'};
    foreach my $wkey (sort workercmp keys(%workers)) {
        next if $wkey eq $TOTAL;
        my $w = $workers{$wkey};
        my $trans = $w->{'trans'};
        foreach my $tindex (sort spcmp keys(%$trans)) {
            if (!defined($ttrans->{$tindex})) {
                $ttrans->{$tindex} = {'time' => 0,
                                      'count' => 0};
            }
            $ttrans->{$tindex}->{'time'} += $trans->{$tindex}->{'time'};
            $ttrans->{$tindex}->{'count'} += $trans->{$tindex}->{'count'};
        }
    }

    return;
}

# ----------------------------------------------------------------------

sub getstarttimes {
    $thetrans = 'Starting->WaitingForWork';
    %time = ();
    @notime = ();
    my $wkey0;
    foreach my $wkey (keys(%workers)) {
        next if ($wkey eq $TOTAL);
        my $w = $workers{$wkey};
        my $t = $w->{'trans'};
        my $t1 = $t->{$thetrans};
        if (!defined($t1->{'count'}) || $t1->{'count'} == 0) {
            push @notime, $wkey;
            next;
        }
        $time{$wkey} = $t1->{'time'} / $t1->{'count'};
        $wkey0 = $wkey;
    }
    ($mintime,$minwkey) = ($time{$wkey0},$wkey0);
    ($maxtime,$maxwkey) = ($time{$wkey0},$wkey0);
    foreach my $wkey (keys(%time)) {
        if ($time{$wkey} < $mintime) { ($mintime,$minwkey) = ($time{$wkey},$wkey); };
        if ($time{$wkey} > $maxtime) { ($maxtime,$maxwkey) = ($time{$wkey},$wkey); };
    }

    return;
}

# ----------------------------------------------------------------------

# compare two workers

sub workercmp ($$) {
    my ($a,$b) = @_;
    my ($aa) = ($a =~ m/^.*?\[(\d+)\]/);
    defined($aa) or $aa = 999999999;
    my ($bb) = ($b =~ m/^.*?\[(\d+)\]/);
    defined($bb) or $bb = 999999999;
    $aa <=> $bb;
}

# compare two states (assumes $stateorder is available)

sub statecmp ($$) {
    my ($a,$b) = @_;
    $stateorder{$a} <=> $stateorder{$b}
}

# compare two state pairs (assumes $sporder is available)

sub spcmp ($$) {
    my ($a,$b) = @_;
    $sporder{$a} <=> $sporder{$b}
}

# compute the maximum key length of a hash

sub maxkeylen {
    my ($href) = @_;
    my $maxlen = 0;
    foreach my $key (keys(%$href)) {
        if (length($key) > $maxlen) {
            $maxlen = length($key);
        }
    }
    $maxlen;
}

# ----------------------------------------------------------------------

# extract description and state from a checker output file
# (given file to read, and basename to use if no state known)

sub gettraceinfo {
    my ($file,$basename) = @_;

    my ($tracefile, $description, $state);

    open IN2, "<$file"
        or die "Couldn't open file $file for reading: $!\n";

    $tracefile = "unknown";
    while (<IN2>) {
        if (/^==Working on trace file (?:<a href=[^>]*>)?([^<]*)/) {
            $tracefile = $1;
            chomp $tracefile;
            last;
        }
    }
    $tracefile =~ s/^==Working on trace file //;

    if (open(IN22, "<$tracefile")) {
        $description = <IN22>;
        $description .= <IN22>;
        chomp $description;
        close IN22
            or die "Couldn't close tracefile $tracefile for reading: $!\n";
    } else {
        $description = "unknown";
    }

    seek IN2,-65536,2;
    while (<IN2>) {
        last if /^==(Trace|Complicated constraint list ends)/;
    }
    if (!defined($_)) {
        $state = "**Trace $basename INCOMPLETE";
    } elsif (/Complicated constraint list ends/) {
        $state = "==Trace $basename TOO_COMPLICATED";
    } else {
        $state = $_;
        chomp $state;
        $state =~ s/:$//;
    }

    close IN2
        or die "Couldn't close file $file for reading: $!\n";

    return ($tracefile,$description,$state);
}

# ----------------------------------------------------------------------

sub gettracelengths {
    my ($tracedir) = @_;

    my %tracelengths = ();

    if (!(open IN3, "<$tracedir/tracelengths.dat")) {
        warn "Couldn't open tracelengths.dat in $tracedir: $!\n";
        return \%tracelengths;
    }

    while (<IN3>) {
        my ($trace,$len) = /^(\S+)\s+(\S+)$/;
        $tracelengths{$trace} = $len;
    }

    close IN3
        or die "Couldn't close tracelengths.dat in $tracedir: $!\n";

    return \%tracelengths;
}

# ----------------------------------------------------------------------

1;
