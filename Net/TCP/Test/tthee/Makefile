OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep

OCAMLCOPT=-I $(OCAMLLIBDIR) -I ../common -I ../ocamlext -I ../ocamllib
OCAMLREQLIBS=
DEP=../common/*.cmxa ../ocamllib/*.cmxa ../ocamlext/*.cmxa

RM=rm -f

TARGETS=mergelib.cmo tthee.cmo ttheehelper.cmo
INTERFS=mergelib.cmi tthee.cmi ttheehelper.cmi

all: tthee.cma tthee.cmxa

tthee.cma: $(INTERFS) $(TARGETS) $(DEP)
	$(OCAMLC) -thread -a -o $@ $(TARGETS)

tthee.cmxa: $(INTERFS) $(TARGETS:.cmo=.cmx) $(DEP)
	$(OCAMLOPT) -thread -a -o tthee.cmxa $(TARGETS:.cmo=.cmx)

clean:
	$(RM) $(INTERFS) $(TARGETS) *.cm[axio] *.cmxa *.[oa]

realclean: clean
	$(RM) .depend

depend:	.depend

.SUFFIXES:.ml .cmo .mli .cmi .cmx

.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.ml.cmo:
	$(OCAMLC) -thread -c $(OCAMLCOPT) $<

.mli.cmi:
	$(OCAMLC) -thread -c $(OCAMLCOPT) $<

.depend: *.mli *.ml
	$(OCAMLDEP) *.mli *.ml > $@

-include .depend
