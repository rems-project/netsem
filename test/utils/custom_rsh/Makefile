OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLFLAGS=-thread -I $(OCAMLPATH)/../lib/ocaml -I .
OCAMLLIBS=unix.cmxa threads.cmxa
RM=rm -f

all: custom_rsh

custom_rsh:
	$(OCAMLLEX) lexer.mll
	$(OCAMLYACC) parser.mly
	$(OCAMLOPT) -c $(OCAMLFLAGS) parsetypes.mli parsetypes.ml
	$(OCAMLOPT) -c $(OCAMLFLAGS) parser.mli
	$(OCAMLOPT) -c $(OCAMLFLAGS) parser.ml
	$(OCAMLOPT) -c $(OCAMLFLAGS) lexer.ml
	$(OCAMLOPT) -c $(OCAMLFLAGS) custom_rsh.ml
	$(OCAMLOPT) -o $@ $(OCAMLFLAGS) $(OCAMLLIBS) parsetypes.cmx parser.cmx lexer.cmx custom_rsh.cmx

clean:
	$(RM) *.cm* *.o* parser.mli custom_rsh parser.ml lexer.ml

realclean: depend

depend: