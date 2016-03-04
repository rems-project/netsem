# NB this directory was copied from Net/TCP/doc/stream_spec; it
# provides stream_spec.tex to the superdir, however stream_spec.mng
# has been edited since it was copied, in order to refer to other
# parts of the typeset HOL specification; do not expect to be able to
# build a document here

# to refresh the bib data for final doc, type FINAL=true make
# to pull in up-to-date files from spec, make in generated before make-ing here
# this file depends on $(TEXINPUTS) env var

GVPID=$(shell ps -a |grep gv | sed -e "s/ *\([0-9]*\).*/\1/")

################################################################################
# paths (to externals)

# ../? - other sty files we need?
# ../tr.bib - the bib file
# (../)^*HOLDoc - the munger

MNGTOLATEXDIR=../../../../HOLDoc
HOLMNGDIR=../../../HOLDoc
SUPERDIR=..

################################################################################
# executables

DVIPS=dvips
DVIPSFLAGS=-t a4 -Ppdf -j0 -G0
DVIPSFLAGSLETTER=-t letter -Ppdf -j1 -G0
DVIPSFLAGSLANDSCAPE=-t a4 -t landscape -Ppdf -j1 -G0
#DVIPSFLAGS=-t letter -Ppdf -j1 -G0

PSTOPDF=ps2pdf

#LATEX=param_size=15000 hash_extra=25000 extra_mem_top=10000000 pool_size=1000000 hugelatex
LATEX=param_size=15000 hash_extra=25000 extra_mem_top=10000000 pool_size=1000000 latex

MNGTOLATEX=${MNGTOLATEXDIR}/mng_to_latex
LTSTOLATEX=$(HOLMNGDIR)/lts_to_latex

################################################################################
# figures
FIGURES=endpoint endtoend absFunCommute absFunCommute2 absFunCommute3 absFunCommute6
FIGURE_PSTEX_TS=$(addsuffix .pstex_t, $(FIGURES))
endpoint_FIG_OPTS=-m 0.25
endtoend_FIG_OPTS=-m 0.25
absFunCommute_FIG_OPTS=-m 1.2
absFunCommute2_FIG_OPTS=-m 0.8
absFunCommute3_FIG_OPTS=-m 0.8
absFunCommute6_FIG_OPTS=-m 0.8

################################################################################
# vars

# Path(s) to miscellaneous TeXery required
EXTRATEXINPUTS=:.:$(SUPERDIR):$(MNGTOLATEXDIR):$(HOLMNGDIR):#     ${HOLDOCDIR}:$(LTSHOLDOCDIR): not needed? don't exist?
IMNFILES=generated/TCP1_auto.imn generated/TCP1_.imn#    TCP3_auto.imn - clashes with TCP1_auto

################################################################################
#
# implicit rules:
#
# route is:
# %.mng       (original LaTeX document with embedded HOL)
#   -> %.tex  (rendered into pure LaTeX)
#   -> %.dvi  (typeset)
#   -> %.ps   (rendered into PostScript)
#   -> %.pdf

%.tex : %.mng $(IMNFILES)
	$(MNGTOLATEX) $(IMNFILES) $*.mng > $*.tex

%.dvi : %.tex
	TEXINPUTS=$(EXTRATEXINPUTS):$(TEXINPUTS) $(LATEX) $*.tex
	#ifeq ($(FINAL),true)
	-bibtex ${<:.tex=}
	TEXINPUTS=$(EXTRATEXINPUTS):$(TEXINPUTS) $(LATEX) $*.tex
	TEXINPUTS=$(EXTRATEXINPUTS):$(TEXINPUTS) $(LATEX) $*.tex
	#else
	#endif

%.ps : %.dvi
	$(DVIPS) $(DVIPSFLAGSLETTER) $*.dvi -o $*.ps
#	-kill -SIGHUP $(GVPID)

%.pdf : %.ps
	$(PSTOPDF) $< $@.tmp
	mv $@.tmp $@

%.pstex %.pstex_t : %.fig
	fig2dev -L pstex               $($*_FIG_OPTS) $< $*.pstex
	fig2dev -L pstex_t -p $*.pstex $($*_FIG_OPTS) $< $*.pstex_t

#stream_spec_crc.mng: Makefile stream_spec.mng
#	sed -e 's/^%.*/%/g' stream_spec.mng > stream_spec_crc.mng

################################################################################
# targets

all: stream_spec.pdf

stream_spec.dvi : stream_spec.tex $(FIGURE_PSTEX_TS) tr.bib Spec1_send3.tex Spec3_send3.tex Spec3_abs_hosts_one_sided.tex trace0963.tex  generated/Spec3_alldoc-inc.tex

clean:
	-rm -f *pstex_t *pstex stream_spec.{aux,bbl,blg,dvi,idx,log,out,ps,tex,pdf} *~

################################################################################
# junk

tjrexport: stream_spec.ps stream_spec.pdf
	cp stream_spec.pdf $(www)/doc/ridge08stream_spec.pdf
	cp stream_spec.ps $(www)/doc/ridge08stream_spec.ps


# keep these around for debugging purposes:
#.PRECIOUS: %.tex %.dvi

