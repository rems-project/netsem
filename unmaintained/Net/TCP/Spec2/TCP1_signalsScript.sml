(* A HOL98 specification of TCP *)

(* The datatype of (Unix) signals *)

(*[ RCSID "$Id: TCP1_signalsScript.sml,v 1.1 2005/07/12 15:42:25 tjr22 Exp $" ]*)

(* standard prefix *)
open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib

open HolDoc

val _ = new_theory "TCP1_signals";

val _ = Version.registerTheory "$RCSfile: TCP1_signalsScript.sml,v $" "$Revision: 1.1 $" "$Date: 2005/07/12 15:42:25 $";

(*: @chapter [[TCP1_signals]] Signal names

This file contains the datatype of signal names, with all the signals
known to POSIX, Linux, and BSD.  The specification does not model signal behaviour in detail, however: it treats them very nondeterministically.

:*)

(*: @section [[signals_signal]] GEN The type of signals

The union of the signals suported by the target architectures.  Names
based on POSIX.

:*)

val _ = Hol_datatype  (* taken directly from POSIX <signal.h> man page *)
  `signal = SIGABRT
          | SIGALRM
          | SIGBUS
          | SIGCHLD
          | SIGCONT
          | SIGFPE
          | SIGHUP
          | SIGILL
          | SIGINT
          | SIGKILL
          | SIGPIPE
          | SIGQUIT
          | SIGSEGV
          | SIGSTOP
          | SIGTERM
          | SIGTSTP
          | SIGTTIN
          | SIGTTOU
          | SIGUSR1
          | SIGUSR2
          | SIGPOLL    (* XSI only *)
          | SIGPROF    (* XSI only *)
          | SIGSYS     (* XSI only *)
          | SIGTRAP    (* XSI only *)
          | SIGURG
          | SIGVTALRM  (* XSI only *)
          | SIGXCPU    (* XSI only *)
          | SIGXFSZ    (* XSI only *)
`
;


val _ = export_theory();
