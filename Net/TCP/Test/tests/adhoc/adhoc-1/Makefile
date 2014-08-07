OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLLEX=$(OCAMLPATH)/ocamllex
RM=rm -f
CC=gcc
MKLIB=ar

OCAMLINCL=-I $(OCAMLLIBDIR) -I ../../../common -I ../../../tthee -I ../../common \
	-I ../../../ocamllib -I ../../autotest
OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa \
	../../../ocamllib/ocamllibnative.cmxa ../../../ocamlext/threadparsing.cmxa \
	../../../ocamlext/platform.cmxa ../../../common/nscommon.cmxa \
	../../../tthee/tthee.cmxa  ../../autotest/common.cmx \
	../../common/testscommon.cmx ../../autotest/simple.cmx
LIBPATHS=-cclib -L../../../nssock -cclib -L../../../ocamlext \
	-cclib -L../../../ocamllib
LIBOUTPUT=common.cmx

all: adhoc-2

adhoc-2: adhoc-2.cmx
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(OCAMLREQLIBS) \
	adhoc-2.cmx $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[iaox] *.cmxa *.o* adhoc-2

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmx .cmi
.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<

-include .depend
