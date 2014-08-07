OCAMLINCL=-I ../../common -I ../../ocamllib \
	  -I $(OCAMLPATH)/../lib/ocaml \
	  -I ../../ocamlext
OCAMLLIB=$(OCAMLPATH)/../lib/ocaml

REQLIBS=$(OCAMLLIB)/unix.cma $(OCAMLLIB)/threads/threads.cma \
	../../ocamllib/ocamllib.cma ../../ocamlext/threadparsing.cma \
	../../ocamlext/platform.cma ../../common/nscommon.cma
NSSOCKLIB=../../nssock/libnssock.a ../../ocamlext/platform.a
NTPLIB=../../common/libntplib.a

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLDEP=$(OCAMLPATH)/ocamldep
RM=rm -f

FILES=parser_test.cmo

all: parser_test

parser_test: $(FILES)
	$(OCAMLC) -o $@ -custom $(OCAMLINCL) $(REQLIBS) $(NSSOCKLIB) \
		$(NTPLIB) $(FILES)

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.o *.a *.cmo *.cmi *.cma *.cmxo *.cmxa
	$(RM) parser_test

realclean: clean
	$(RM) .depend


.SUFFIXES:.ml .mli .cmo .cmi
.mli.cmi:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(OCAMLINCL) $<

-include .depend
