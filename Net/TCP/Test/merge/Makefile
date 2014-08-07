OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml
OCAMLCOPT=-I $(OCAMLLIBDIR) -I ../ocamlext -I ../common -I ../ocamllib -I ../nssock
OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cma $(OCAMLLIBDIR)/threads/threads.cma \
	../ocamlext/platform.cma ../ocamllib/ocamllib.cma ../nssock/libnssock.a  \
	../common/libntplib.a ../ocamlext/threadparsing.cma ../common/nscommon.cma
RM=rm -f

OBJS=mlogger.cmo

all: mlogger

mlogger: $(OBJS)
	$(OCAMLC) -thread -o $@ -custom $(OCAMLCOPT) $(OCAMLREQLIBS) $(OBJS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cmo *.cmi *.o mlogger

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .cmo
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(OCAMLCOPT) $<

-include .depend