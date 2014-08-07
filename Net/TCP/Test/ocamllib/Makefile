NSSOCKLIB=../nssock/libnssock.a

# empty for no, 1 for yes
FRESH?=
NATIVE?=$(if $(FRESH),,1)
fresh=$(if $(FRESH),fresh-,)

ifeq (,$(FRESH))
OCAMLPREFIX=$(OCAMLPATH)/../lib/ocaml
else
OCAMLPREFIX=/home/kw217/Scratch/Fast/lib/$(fresh)ocaml
endif

OCAMLC=$(fresh)ocamlc
OCAMLOPT=$(fresh)ocamlopt
OCAMLDEP=$(fresh)ocamldep
OCAMLMKLIB=$(fresh)ocamlmklib -ocamlc $(OCAMLC) -ocamlopt $(OCAMLOPT)
OCAMLCOPT=-I $(OCAMLPREFIX)/caml -I $(OCAMLPREFIX)
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