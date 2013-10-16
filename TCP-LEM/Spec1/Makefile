SHELL=bash

LEM=lem.sh # local alias for lem, with -lib 

all:
	$(LEM) TCP1_lemSupport.lem TCP1_errors.lem TCP1_signals.lem TCP1_utils.lem  TCP1_baseTypes.lem TCP1_timers.lem TCP1_params.lem

clean:
	rm -f *{.ml,Script.sml}
