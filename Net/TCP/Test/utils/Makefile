SUBDIRS=ns_logger socktools diags conflate

all::
	for i in $(SUBDIRS); do \
	if [ -d $$i ]; then \
	cd $$i && $(MAKE) all; \
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
