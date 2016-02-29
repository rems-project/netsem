NSSOCKLIB=../nssock/libnssock.a

OCAMLPREFIX=$(OCAMLPATH)/../lib/ocaml

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib -ocamlc $(OCAMLC) -ocamlopt $(OCAMLOPT)
OCAMLCOPT=-I $(OCAMLPREFIX) -ccopt "-fPIC"
RM=rm -f

CFILES=camlsupport.c cst2constr.c errmsg.c unixsupport.c \
	prnsupport.c ocamllibc.c
CAMLFILES=ocamllib.ml
CAMLIFACES=ocamllib.mli

LIBPATHS=-cclib -L../nssock -cclib -lnssock -cclib\
	 -L../common -cclib -lntplib

all: $(CAMLIFACES:.mli=.cmi) libocamllib.a $(if $(NATIVE),libocamllibnative.a,)

libocamllib.a: $(CAMLFILES:.ml=.cmo) $(CFILES:.c=.o) $(NSSOCKLIB)
	$(OCAMLMKLIB) -o ocamllib $(CAMLFILES:.ml=.cmo) $(CFILES:.c=.o) \
			    $(NSSOCKLIB)

libocamllibnative.a: $(CAMLFILES:.ml=.cmx) $(CFILES:.c=.o) $(NSSOCKLIB)
	$(OCAMLMKLIB) -o ocamllibnative $(CAMLFILES:.ml=.cmx) $(CFILES:.c=.o) $(LIBPATHS)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.[oa] *.cm[ioax] *.cmxa *.so

realclean: clean
	$(RM) .depend

.SUFFIXES: .c .o .ml .cmo .mli .cmi .cmx
.ml.cmx:
	$(OCAMLOPT) -c $(OCAMLCOPT) $<
.c.o:
	$(OCAMLC) -custom -c $(OCAMLCOPT) $<
.mli.cmi:
	$(OCAMLC) -c $(OCAMLCOPT) $<
.ml.cmo:
	$(OCAMLC) -custom -c $(OCAMLCOPT) $<

-include .depend
