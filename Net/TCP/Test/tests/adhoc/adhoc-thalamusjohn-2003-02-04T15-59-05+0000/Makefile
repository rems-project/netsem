OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep

OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa\
	../../../ocamllib/ocamllibnative.cmxa ../../../ocamlext/threadparsing.cmxa\
	../../../common/nettypes.cmx ../../../common/netconv.cmx\
	../../../common/sock.cmx ../../../common/parserlib.cmx\
	../../../common/holparselib.cmx ../../../common/tcpcbparserlib.cmx\
	../../../common/parser.cmx ../../../common/render.cmx \
	../../../common/librender.cmx ../../../common/lexer.cmx\
	../../../common/holrender.cmx ../../../common/tcpcbrender.cmx\
	../../../common/renderlib.cmx ../../../ocamlext/platform.cmxa \
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
	$(RM) test *.cmx *.cmo *.cma *.cmxa *.o *.cmi .depend

depend: .depend

.SUFFIXES:.ml .mli .cmi .cmx

.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLCOPT) $<

.depend: *.ml
	$(OCAMLDEP) *.mli *.ml > $@

-include .depend
