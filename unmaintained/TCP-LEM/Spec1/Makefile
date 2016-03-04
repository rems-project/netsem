SHELL=bash

LEM=lem.sh # local alias for lem, with -lib set appropriately

LEMS=TCP1_lemSupport.lem TCP1_errors.lem TCP1_signals.lem TCP1_utils.lem  TCP1_baseTypes.lem TCP1_timers.lem TCP1_params.lem TCP1_netTypes.lem TCP1_preHostTypes.lem TCP1_LIBinterface.lem TCP1_hostTypes.lem TCP1_host0.lem TCP1_ruleids.lem TCP1_auxFns.lem TCP1_hostLTS.lem # TCP1_net.lem TCP1_net1.lem 

# TCP1_evalSupport.lem - this file is not relevant to the spec; it
# defines a simple host, presumably used for testing purposes

all:
	$(LEM) $(LEMS)

hol:
	$(LEM) -hol TCP1_lemSupport.lem

FIXMES:
	-grep FIXME TCP1_errors.lem TCP1_signals.lem TCP1_utils.lem TCP1_baseTypes.lem TCP1_timers.lem TCP1_params.lem TCP1_netTypes.lem TCP1_preHostTypes.lem TCP1_LIBinterface.lem TCP1_hostTypes.lem TCP1_host0.lem TCP1_ruleids.lem TCP1_auxFns.lem TCP1_hostLTS.lem 

types:
	$(LEM) -print_env $(LEMS)

clean:
	rm -f *{.ml,Script.sml}
