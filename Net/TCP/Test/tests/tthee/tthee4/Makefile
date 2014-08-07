OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep

OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa \
	../../../ocamllib/ocamllibnative.cmxa ../../../ocamlext/threadparsing.cmxa \
	../../../ocamlext/platform.cmxa ../../../common/nscommon.cmxa \
	../../../tthee/tthee.cmxa ../../common/testscommon.cmx

LIBPATHS=-cclib -L../../../nssock -cclib -L../../../ocamlext/
OCAMLCOPT=-I $(OCAMLLIBDIR) -I ../../../common -I ../../../ocamlext\
	 -I ../../../tthee -I ../../../ocamllib -I ../../common/
RM=rm -f

TARGETS=test.cmx

all: test

test: $(TARGETS) $(OCAMLREQLIBS)
	$(OCAMLOPT) -thread -o $@ $(OCAMLCOPT) $(OCAMLREQLIBS) $(TARGETS) $(LIBPATHS)

clean:
	$(RM) test *.cm[xoia] *.cmxa *.o

realclean: clean
	$(RM) .depend

depend: .depend

.SUFFIXES:.ml .mli .cmi .cmx

.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.depend: *.ml
	$(OCAMLDEP) *.mli *.ml > $@

-include .depend
