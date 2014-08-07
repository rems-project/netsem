OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep

OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa\
	../../ocamllib/ocamllibnative.cmxa ../../ocamlext/threadparsing.cmxa\
	../../common/nscommon.cmxa ../../ocamlext/platform.cmxa \
	../../tthee/tthee.cmxa

LIBPATHS=-cclib -L../../nssock -cclib -L../../ocamlext/
OCAMLCOPT=-I $(OCAMLLIBDIR) -I ../../common -I ../../ocamlext\
	 -I ../../tthee -I ../../ocamllib
RM=rm -f

TARGETS=testscommon.cmx

all: test

test: $(TARGETS)

clean:
	$(RM) test *.cm[oaix] *.cmxa *.o

realclean: clean
	$(RM) .depend

depend: .depend

.SUFFIXES:.ml .mli .cmi .cmx

.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.depend: *.mli *.ml
	$(OCAMLDEP) *.mli *.ml > $@

-include .depend
