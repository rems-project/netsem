OCAMLINCL=-I ../common -I ../ocamllib -I $(OCAMLPATH)/../lib/ocaml \
	  -I ../ocamlext
OCAMLLIB=$(OCAMLPATH)/../lib/ocaml

REQLIBS=$(OCAMLLIB)/unix.cma $(OCAMLLIB)/threads/threads.cma \
	../ocamllib/ocamllib.cma ../ocamlext/threadparsing.cma \
	../ocamlext/platform.cma ../common/nscommon.cma
NSSOCKLIB=../nssock/libnssock.a ../ocamlext/platform.a
NTPLIB=../common/libntplib.a

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLDEP=$(OCAMLPATH)/ocamldep
RM=rm -f

OBJS=libd.cmo

all: libd

libd: $(OBJS) $(NSSOCKLIB) $(NTPLIB) $(REQLIBS)
	$(OCAMLC) -thread -o $@ -custom $(OCAMLINCL) $(REQLIBS) $(NSSOCKLIB) \
		$(NTPLIB) $(OBJS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.[oa] *.cm[oiax] libd

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmo .cmi
.mli.cmi:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<

-include .depend
