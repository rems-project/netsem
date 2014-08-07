OCAMLC=$(OCAMLPATH)/ocamlc
OCAMLOPT=$(OCAMLPATH)/ocamlopt
OCAMLLIBDIR=$(OCAMLPATH)/../lib/ocaml
OCAMLMKLIB=$(OCAMLPATH)/ocamlmklib
OCAMLDEP=$(OCAMLPATH)/ocamldep
OCAMLYACC=$(OCAMLPATH)/ocamlyacc
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLDOC=$(OCAMLPATH)/ocamldoc
RM=rm -f
CC=gcc
MKDEP=makedepend
MKLIB=ar

OCAMLOPTIONS=-c -custom
OCAMLLIBS=-I $(OCAMLLIBDIR) -I ../ocamlext/ -I ../ocamllib/

# targets associated with printing, not netipreass net2hol, which are slurper stuff, and hol2net which is injector
PRINTTARGETS=nettypes.cmo netconv.cmo sock.cmo \
	libcalls.cmo holtypes.cmo holparselib.cmo \
	holrender.cmo tcpcbtypes.cmo tcpcbparserlib.cmo parserlib.cmo\
	librender.cmo tcpcbrender.cmo renderlib.cmo parser.cmo lexer.cmo

TARGETS=$(PRINTTARGETS) netipreass.cmo net2hol.cmo hol2net.cmo

CLEAN_PARSER=parser.ml parser.mli lexer.ml

all: nscommon.cma nscommon.cmxa libntplib.a

libntplib.a: ntpheader.o
	$(MKLIB) -r $@ ntpheader.o

nscommon.cma: parser.ml lexer.ml $(TARGETS)
	$(OCAMLC) -thread -a -o $@ $(TARGETS)

nscommon.cmxa: parser.ml lexer.ml $(TARGETS:.cmo=.cmx)
	$(OCAMLOPT) -thread -a -o $@ $(TARGETS:.cmo=.cmx)

parser.ml: parser.mly
	$(OCAMLYACC) parser.mly
	../ocamlext/parser_hack_script parser

parser.mli: parser.ml

lexer.ml: lexer.mll
	$(OCAMLLEX) lexer.mll

clean:	cleanparser
	$(RM) *.cm[oiax] *.cmxa $(TARGETS) $(INTERFS)
	-$(RM) ocamldoc.out ocamldoc.ps

cleanparser:
	$(RM) $(CLEAN_PARSER) *.[ao]

realclean: clean
	$(RM) .depend .depend2

depend:	parser.ml lexer.ml
	$(OCAMLDEP) *.mli *.ml > .depend
	$(MKDEP) -f- *.c > .dependc

# make ocamldoc
ocamldoc.ps: all
	-$(OCAMLDOC) -dot $(OCAMLLIBS) $(PRINTTARGETS:.cmo=.ml)
	dot -Tps ocamldoc.out >ocamldoc.ps

.SUFFIXES:.ml .cmo .mli .cmi .cmx
.mli.cmi:
	$(OCAMLC) -thread $(OCAMLOPTIONS) $(OCAMLLIBS) $<
.ml.cmo:
	$(OCAMLC) -thread $(OCAMLOPTIONS) $(OCAMLLIBS) $<
.ml.cmx:
	$(OCAMLOPT) -thread -c $(OCAMLLIBS) $<
.c.o:
	$(CC) -c $<

-include .depend
-include .dependc
