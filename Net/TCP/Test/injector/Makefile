OCAMLINCL=-I ../common -I ../ocamlext -I $(OCAMLPATH)/../lib/ocaml \
	-I ../ocamllib

REQLIBS=$(OCAMLPATH)/../lib/ocaml/unix.cma \
	$(OCAMLPATH)/../lib/ocaml/threads/threads.cma \
	../ocamlext/rawsock.cma ../ocamlext/platform.cma \
	../ocamllib/ocamllib.cma ../ocamlext/threadparsing.cma \
	../common/nscommon.cma
NSSOCKLIB=../nssock/libnssock.a
NTPLIB=../common/libntplib.a

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLLEX$(OCAMLPATH)/=ocamllex
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLDEP=$(OCAMLPATH)/ocamldep
RM=rm -f

OBJS=injector.cmo

all: injector

injector: $(OBJS) $(REQLIBS) $(NSSOCKLIB) $(NTPLIB)
	$(OCAMLC) -o $@ -custom $(OCAMLINCL) $(NSSOCKLIB) $(REQLIBS) \
	$(NTPLIB) $(OBJS) -ccopt -L../ocamllib

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.[oa] *.cm[oiax] injector

realclean: clean
	$(RM) .depend


.SUFFIXES:.ml .mli .cmo .cmi
.mli.cmi:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<


-include .depend