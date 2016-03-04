#
# To make things-that-arent-great-but.{ps|pdf}, type:
#
# make updatelocal
# make doc
#

# read user configuration - local to this directory:
include munge.mk

DVIPS=dvips
PSTOPDF=ps2pdf
LATEX=hugelatex

DVIPSFLAGS=-t a4 -Ppdf -j1 -G0

#
# list of .imn include files to use:
#
SPECDIR=../Spec1
SPECIMNS=TCP1_auto.imn TCP1_.imn
LOCALIMN=localcopy-TCP1_star.imn

ifdef DIRECT
IMNFILES=$(addprefix $(SPECDIR)/, $(SPECIMNS))
else
IMNFILES=$(LOCALIMN)
endif

#
# OCaml stuff
#
OCAMLDIR = /home/pes20/bin
OCAML = ocaml
OCAMLC = ${OCAMLDIR}/ocamlc.opt
OCAMLOPT = ${OCAMLDIR}/ocamlopt.opt
OCAML_SOURCES = /home/pes20/ocaml-3.02

#
# Insert here files to keep, that would otherwise be deleted by make clean
#
KEEPFILES = stevens-fig.ps timers.tex

all: TCP1_level0

TCP1_level0_rules.tex TCP1_level0_small.dot TCP1_level0_big.dot: TCP1_level0.ml
	$(OCAML) TCP1_level0.ml

%.ps: %.dot
	dot -s72 -Tps $< -o $@

TCP1_level0: TCP1_level0_small.ps TCP1_level0_big.ps TCP1_level0_big_a4.ps


TCP1-neato: TCP1_level0.ps

TCP1_level0.ps: TCP1_level0.dot
	neato -s72 -n2 -Tps TCP1_level0.dot -o TCP1_level0.ps


TCP1_level0_big_a4.ps: TCP1_level0_big.ps
	perl -pe '$$_ .= "2 sqrt 0.25 mul dup scale\n" if /^%%BeginProlog/' < $< > $@

doc:	things-which-arent-great-but.ps things-which-arent-great-but.pdf

exec3:	exec3.ml
	$(OCAMLOPT) -thread -cclib -lunix -o exec3 unix.cmxa threads.cmxa exec3.ml

exec2:	exec2.ml
	$(OCAMLOPT) -thread -cclib -lunix -o exec2 unix.cmxa threads.cmxa exec2.ml

%.tex:  %.mng $(IMNFILES)
	$(MNGTOLATEX) $(IMNFILES) $*.mng > $@

%.dvi:	%.tex
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) $<

%.ps:	%.dvi
	$(DVIPS) $(DVIPSFLAGS) $< -o $@.tmp
	mv $@.tmp $@

%.pdf:	%.ps
	$(PSTOPDF) $< $@.tmp
	mv $@.tmp $@

clean:
	for keep in $(KEEPFILES); do mv $$keep $$keep.bat; done
	rm -f exec2 exec3 *.tex *.dvi *.ps *.pdf *.aux *.log
	for keep in $(KEEPFILES); do mv $$keep.bat $$keep; done
	rm -f TCP1_level0.ps TCP1_level0.dot
	rm -f TCP1_level0_big{,_a4}.{dot,ps}
	rm -f TCP1_level0_small.{dot,ps}
	rm -f TCP1_level0_rules.tex

updatelocal:
	(cd $(SPECDIR); $(MAKE) $(SPECIMNS))
	cat $(addprefix $(SPECDIR)/, $(SPECIMNS)) > $(LOCALIMN)
