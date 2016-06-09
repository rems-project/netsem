OCAMLLIB=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLLEX=$(OCAMLPATH)/ocamllex
RM=rm -f
CC=cc
MKLIB=ar

OCAMLINCL=-I ../../common -I ../../ocamllib \
	  -I $(OCAMLPATH)/../lib/ocaml \
	  -I ../../ocamlext

REQLIBS=$(OCAMLLIB)/unix.cmxa $(OCAMLLIB)/threads/threads.cmxa str.cmxa \
	../../ocamllib/ocamllibnative.cmxa ../../ocamlext/threadparsing.cmxa \
	../../ocamlext/platform.cmxa ../../common/nscommon.cmxa
LIBPATHS=-cclib -L../../nssock -cclib -L../../ocamlext -cclib -L../../ocamllib

OBJS=tracediff.cmx

all: tracediff

tracediff: $(OBJS)
	$(OCAMLOPT) -thread -o $@ $(OCAMLINCL) $(REQLIBS) \
	$(OBJS) $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[ioxa] *.cmxa *.o* mkdiag
	$(RM) *.{aux,log,dvi,toc} *~

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmx .cmi
.mli.cmi:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLINCL) $<

-include .depend
