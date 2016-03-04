OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLDEP=$(OCAMLPATH)/ocamldep
CC=cc
MKDEP=$(CC) -M
RM=rm -f

OCAMLDIR=$(OCAMLPATH)/../lib/ocaml
OCAMLLIBS=$(OCAMLDIR)/unix.cmxa $(OCAMLDIR)/threads/threads.cmxa \
	../ocamlext/rawsock.cmxa ../ocamlext/platform.cmxa
OCAMLINCL=-I $(OCAMLDIR)/lib/ocaml/ -I $(OCAMLDIR)/lib/ocaml/threads/ \
	-I ../ocamlext/
INCLUDEDIRS=-I$(X86_PATH)/include
LIBDIRS=-L$(X86_PATH)/lib

all: pcapslurp fileinject injectslurp slurpinject

pcapslurp: pcapslurp.o
	$(CC) -o $@ $(LIBDIRS) pcapslurp.o -lpcap

fileinject: fileinject.o
	$(CC) -o $@ fileinject.o

injectslurp: errors.cmx injectslurp.cmx
	$(OCAMLOPT) -o $@ $(OCAMLINCL) $(OCAMLLIBS) injectslurp.cmx

slurpinject: errors.cmx parser.cmx lexer.cmx slurpinject.cmx
	$(OCAMLOPT) -o $@ $(OCAMLINCL) $(OCAMLLIBS) errors.cmx\
		parser.cmx lexer.cmx slurpinject.cmx

depend: parser.ml lexer.ml parser.mli
	$(OCAMLDEP) *.mli *.ml > .depend
	$(MKDEP) $(INCLUDEDIRS) *.c > .dependc

clean:
	$(RM) *.o* *.lib *.a *.cm* pcapslurp fileinject\
	slurpinject injectslurp parser.ml parser.mli lexer.ml

realclean: clean
	$(RM) .depend .dependc

.SUFFIXES:.c .o .ml .cmx .mly .mll .mli .cmi
.c.o:
	$(CC) -c $(INCLUDEDIRS) $<
.mli.cmi:
	$(OCAMLOPT) -c $(OCAMLINCL) -thread $(OCAMLLIBS) $<
.ml.cmx:
	$(OCAMLOPT) -c $(OCAMLINCL) -thread $(OCAMLLIBS) $<
.mly.ml:
	$(OCAMLYACC) $<
.mly.mli:
	$(OCAMLYACC) $<
.mll.ml:
	$(OCAMLLEX) $<

-include .depend
-include .dependc
