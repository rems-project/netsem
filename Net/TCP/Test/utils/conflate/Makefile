# at some point, go through this and remove unnecessary dependencies

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

OCAMLINCL=-I $(OCAMLLIBDIR) -I ../../common \
	-I ../../ocamllib -I ../../ocamlext
OCAMLREQLIBS=$(OCAMLLIBDIR)/unix.cmxa $(OCAMLLIBDIR)/threads/threads.cmxa \
        ../../ocamllib/ocamllibnative.cmxa ../../ocamlext/threadparsing.cmxa \
	../../common/nscommon.cmxa
LIBPATHS=-cclib -L../../nssock -cclib -L../../ocamlext \
        -cclib -L../../ocamllib
#LIBOUTPUT=common.cmx

all: conflate

conflate: conflate.cmx
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(OCAMLREQLIBS) \
	conflate.cmx $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[iaox] *.cmxa *.o* conflate

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmx .cmi
.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<

-include .depend
