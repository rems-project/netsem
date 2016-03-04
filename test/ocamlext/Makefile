OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLDEP=$(OCAMLPATH)/ocamldep
CAMLOPTS=-I $(OCAMLPATH)/../byterun -I $(OCAMLPATH)/../otherlibs/unix \
	-I $(OCAMLPATH)/../otherlibs/str -I $(OCAMLPATH)/../lib/ocaml/ -I $(OCAMLPATH)/../lib/ocaml/caml
REQOCAMLLIBS=$(OCAMLPATH)/../lib/ocaml/unix.cma $(OCAMLPATH)/../lib/ocaml/str.cma
MKLIB=$(OCAMLPATH)/ocamlmklib -ocamlc $(OCAMLC) -ocamlopt $(OCAMLOPT)

RM=rm -f

RCFILES=rawsockc.o
RMLIFILES=rawsock.mli
RMLFILES=rawsock.ml

PCFILES=platformc.c
PMLIFILES=platform.mli
PMLFILES=platform.ml

TPMLFILES=threadparsing.ml
TPMLIFILES=threadparsing.mli
PARSERHACK=parser_hack_script.ml

all: librawsock.a libplatform.a threadparsing.cma threadparsing.cmxa parser_hack_script

librawsock.a: $(RCFILES:.c=.o) $(RMLIFILES:.mli=.cmi)\
	 $(RMLFILES:.ml=.cmo) $(RMLFILES:.ml=.cmx)
	$(MKLIB) -o rawsock $(RMLFILES:.ml=.cmo) $(RCFILES:.c=.o)
	$(MKLIB) -o rawsock $(RMLFILES:.ml=.cmx) $(RCFILES:.c=.o)

libplatform.a: $(PCFILES:.c=.o) $(PMLIFILES:.mli=.cmi)\
	$(PMLFILES:.ml=.cmo) $(PMLFILES:.ml=.cmx)
	$(MKLIB) -o platform $(PMLFILES:.ml=.cmo) $(PCFILES:.c=.o)
	$(MKLIB) -o platform $(PMLFILES:.ml=.cmx) $(PCFILES:.c=.o)

threadparsing.cma: $(TPMLIFILES:.mli=.cmi) $(TPMLFILES:.ml=.cmo)
	$(OCAMLC) -thread -a -o threadparsing.cma $(TPMLFILES:.ml=.cmo)

threadparsing.cmxa: $(TPMLIFILES:.mli=.cmi) $(TPMLFILES:.ml=.cmx)
	$(OCAMLOPT) -thread -a -o threadparsing.cmxa $(TPMLFILES:.ml=.cmx)

parser_hack_script: $(PARSERHACK:.ml=.cmo)
	$(OCAMLC) -o $@ $(CAMLOPTS) $(REQOCAMLLIBS) $(PARSERHACK:.ml=.cmo)

depend: parser_hack_script
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[oaix] *.[oa] *.cmxa *.so parser_hack_script

realclean: clean
	$(RM) .depend

.SUFFIXES: .c .o .ml .cmo .mli .cmi .cmx
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLOPTS) $<
.c.o:
	$(OCAMLC) -thread -c -custom $(CAMLOPTS) $<
.mli.cmi:
	$(OCAMLC) -thread -c -custom $(CAMLOPTS) $<
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(CAMLOPTS) $<

-include .depend
