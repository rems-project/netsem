OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLDEP=$(OCAMLPATH)/ocamldep
RM=rm -f

OCAMLDIR=$(OCAMLPATH)/../lib/ocaml
OCAMLLIBS=$(OCAMLDIR)/unix.cma $(OCAMLDIR)/threads/threads.cma \
  ../ocamllib/ocamllib.cma ../ocamlext/threadparsing.cma \
  ../common/nscommon.cma ../ocamlext/platform.cma
OCAMLINCL=-I $(OCAMLDIR)/lib/ocaml -I ../ocamlext -I ../common \
	-I ../ocamllib
OTHERLIBS=../nssock/libnssock.a ../common/libntplib.a

all: mirror

mirror:	mirror.cmo
	$(OCAMLC) -o $@ -custom $(OCAMLINCL) $(OCAMLLIBS) $(OTHERLIBS) mirror.cmo

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.o *.cm[oi] mirror

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmi .cmo
.mli.cmi:
	$(OCAMLC) -c $(OCAMLINCL) -thread $(OCAMLLIBS) $<
.ml.cmo:
	$(OCAMLC) -c $(OCAMLINCL) -thread $(OCAMLLIBS) $<

-include .depend
