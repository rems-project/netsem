# at some point, go through this and remove unnecessary dependencies

OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLLEX=$(OCAMLPATH)/ocamllex
RM=rm -f
CC=cc
MKLIB=ar

OCAMLINCL=-I $(OCAMLLIBDIR) -I ../../common -I ../../tthee \
	-I ../../ocamllib -I ../../ocamlext
OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa \
	../../ocamllib/ocamllibnative.cmxa ../../ocamlext/threadparsing.cmxa \
	../../ocamlext/platform.cmxa ../../common/nscommon.cmxa
#	../../tthee/tthee.cmxa ../../tests/common/testscommon.cmx
LIBPATHS=-cclib -L../../nssock -cclib -L../../ocamlext \
	-cclib -L../../ocamllib
#LIBOUTPUT=common.cmx

all: test test_spec3

test: test.cmx
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(OCAMLREQLIBS) \
	test.cmx $(LIBPATHS)

test_spec3: test_spec3.cmx
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(OCAMLREQLIBS) \
	test_spec3.cmx $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[iaox] *.cmxa *.o* test test_spec3

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmx .cmi
.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<

-include .depend
