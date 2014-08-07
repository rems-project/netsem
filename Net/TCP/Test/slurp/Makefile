X86_PATH=/usr/groups/netsem/ix86_linux-glibc-2.3.2-27.9
INCLUDEDIRS=-I $(OCAMLPATH)/../byterun -I $(X86_PATH)/include \
	-I $(OCAMLPATH)/../lib/ocaml/ -I ../ocamlext/ -I ../common/
OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml
REQLIBS=unix.cma threads.cma ../ocamlext/platform.cma ../common/nscommon.cma
LIBDIRS=-L$(X86_PATH)/lib

OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLCOPTS=$(INCLUDEDIRS)
OCAMLLIBOPTS=$(LIBDIRS)
RM=rm -f

OFILES=pcapfile.cmo pcapinterface.cmo debugrenderer.cmo slurp.cmo pcapinterfacec.o

all: slurp

slurp: 	$(OFILES) ../ocamlext/platform.cma ../common/nscommon.cma
	$(OCAMLC) -thread -o $@ -custom $(OCAMLCOPTS) $(REQLIBS) \
		$(OFILES) -cclib $(OCAMLLIBOPTS) -cclib -lpcap

depend:
	$(OCAMLDEP) *.mli *.ml > .depend

clean:
	$(RM) *.cm[ioax] *.[oa] *.cmxa slurp

realclean: clean
	$(RM) .depend

.SUFFIXES:.ml .mli .cmi .cmo .c .o
.mli.cmi:
	$(OCAMLC) -thread -c -custom $(OCAMLCOPTS) $<
.ml.cmo:
	$(OCAMLC) -thread -c -custom $(OCAMLCOPTS) $<
.c.o:
	$(OCAMLC) -thread -c -custom $(OCAMLCOPTS) $<

-include .depend
