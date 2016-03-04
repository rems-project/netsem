SUBDIRS=check

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

# commands to test build-diags3
foo:
	/home/pes20/Net/TCP/Test/scripts/build-diags3 /usr/groups/tthee/batch/autotest-tcp-2004-10-01T16\:28\:00+0100/  /auto/groups/tthee-scratch/check/check-2004-12-16T20\:04\:23+0000/trace0309.out.html

bar:
	/home/pes20/Net/TCP/Test/scripts/build-diags3 /usr/groups/tthee/batch/autotest-tcp-2004-10-01T16\:28\:00+0100/  /auto/groups/tthee-scratch/check/check-2004-12-16T20\:04\:23+0000/

baz:
	/home/pes20/Net/TCP/Test/scripts/build-diags3 /usr/groups/tthee/batch/demo-traces  /auto/groups/tthee-scratch/check/check-2004-12-18T14\:09\:26+0000/trace5000.out.html
	/home/pes20/Net/TCP/Test/scripts/build-diags3 /usr/groups/tthee/batch/demo-traces  /auto/groups/tthee-scratch/check/check-2004-12-18T14\:09\:26+0000/trace5002.out.html

