OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLDOC=$(OCAMLPATH)/ocamldoc
RM=rm -f
CC=gcc
MKLIB=ar

OCAMLINCL=-I $(OCAMLLIBDIR) -I ../../common -I ../../tthee -I ../common \
	-I ../../ocamllib
REQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa \
	../../ocamllib/ocamllibnative.cmxa ../../ocamlext/threadparsing.cmxa\
	../../ocamlext/platform.cmxa ../../common/nscommon.cmxa\
	../../tthee/tthee.cmxa ../common/testscommon.cmx
LIBPATHS=-cclib -L../../nssock -cclib -L../../ocamlext -cclib -L../../ocamllib

OBJS=common.cmx simple.cmx dual.cmx dualdriven.cmx common_udp.cmx  \
	dualdriven_udp.cmx socket.cmx bind.cmx bind_2.cmx bind_udp.cmx\
	connect.cmx connect_udp.cmx listen.cmx accept.cmx dup.cmx dupfd.cmx \
	drivetest.cmx close.cmx disconnect.cmx getifaddrs.cmx \
	getsocklistening.cmx getnames.cmx sockbopt.cmx socknopt.cmx \
	socktopt.cmx sockatmark_udp.cmx shutdown.cmx send.cmx recv.cmx \
	send_to.cmx recv_from.cmx fileflags.cmx getsockerr.cmx deliver_in.cmx \
	timers.cmx deliver_in_3.cmx deliver_icmp.cmx loopback.cmx pselect.cmx \
  demo.cmx network.cmx loss.cmx autotest.cmx

all: autotest

autotest: $(OBJS) $(REQLIBS)
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(REQLIBS) \
	$(OBJS) $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

ocamldoc.ps: all
	-$(OCAMLDOC) -dot $(OCAMLINCL) -I +threads $(OBJS:.cmx=.ml)
	dot -Tps ocamldoc.out >ocamldoc.ps

clean:
	$(RM) *.cm[ioxa] *.cmxa *.o* autotest

realclean: clean
	$(RM) .depend


.SUFFIXES:.ml .mli .cmx .cmi
.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<


-include .depend
