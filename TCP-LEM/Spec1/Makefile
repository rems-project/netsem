SHELL=bash

LEM=lem.sh # local alias for lem, with -lib 

LEMS=TCP1_lemSupport.lem TCP1_errors.lem TCP1_signals.lem TCP1_utils.lem  TCP1_baseTypes.lem TCP1_timers.lem TCP1_params.lem TCP1_netTypes.lem TCP1_preHostTypes.lem TCP1_LIBinterface.lem TCP1_hostTypes.lem TCP1_host0.lem TCP1_ruleids.lem TCP1_auxFns.lem

all:
	$(LEM) $(LEMS)

types:
	$(LEM) -print_types $(LEMS)

clean:
	rm -f *{.ml,Script.sml}
