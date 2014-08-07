MINIMAL=nssock ocamllib ocamlext common libd slurp \
	injector mirror
SUBDIRS=$(MINIMAL) identtest tthee tests utils scripts

all::
	for i in $(SUBDIRS); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) all; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

min::
	for i in $(MINIMAL); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) all; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

mindepend::
	for i in $(MINIMAL); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) depend; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

minrealclean::
	for i in $(MINIMAL); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) realclean; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

clean::
	for i in $(SUBDIRS); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) clean; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

realclean::
	for i in $(SUBDIRS); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) realclean; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done

depend::
	for i in $(SUBDIRS); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) depend; \
	if [ $$? -eq 0 ] ;  then true && cd ..; else exit 1; \
	fi; \
	fi; \
	done
