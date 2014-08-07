 # Makefile for TCP/Spec3.
#
# lts_to_latex Out_of_memory on TCP3_hostLTS.tmp2-tex, fix by setting
# heap limit very large eg in BASH
#
# export OCAMLRUNPARAM='h=256M'


.DEFAULT_GOAL=alldoc.ps
.SUFFIXES:
SHELL=bash

LATEX=latex
PDFLATEX=extra_mem_top=1000000 pdflatex
DVIPS=dvips
PSTOPDF=ps2pdf

# read user configuration:
include munge.mk

LTSHOLDOCDIR=../../HOLDoc
LTS_TO_LATEX=$(LTSHOLDOCDIR)/lts_to_latex
MNG_TO_LATEX=${HOLDOCDIR}/mng_to_latex

DVIPSFLAGS=-t a4 -Ppdf -j1 -G0

# IMNFILES order may be significant (not sure).
IMNFILES=TCP3_auto.imn TCP3_.imn
# IMNFILES=TCP3_auto.imn ../Spec1/TCP1_.imn ../Spec1/TCP1_auto_hacked.imn
EXTRATEXINPUTS=${HOLDOCDIR}:$(LTSHOLDOCDIR):stream_spec
EXTRABIBINPUTS=../doc# for tr.bib
OTHERTEXFILES=#inetheaders.inc only for Spec1

# lists of files:

# SPECTHEORYFILES are the for-public-consumption files, containing no evaluator info
#  (listed here in a sensible order)
#   TCP1_utilsScript.sml         \
#   TCP1_errorsScript.sml	       \
#   TCP1_signalsScript.sml       \
#   TCP1_baseTypesScript.sml     \
#   TCP1_netTypesScript.sml      \
#   TCP1_LIBinterfaceScript.sml  \
#   TCP1_host0Script.sml	       \
#   TCP1_ruleidsScript.sml       \
#   TCP1_timersScript.sml	       \
#   TCP1_preHostTypesScript.sml  \
#   TCP1_hostTypesScript.sml     \
#   TCP1_paramsScript.sml        \
#   TCP1_auxFnsScript.sml	       \
#   TCP1_hostLTSScript.sml       \
#   TCP1_netScript.sml           \
#   TCP1_net1Script.sml          \
#   TCP1_evalSupportScript.sml
SPECTHEORYFILES=\
   TCP3_hostTypesScript.sml     \
   TCP3_streamTypesScript.sml   \
   TCP3_host0Script.sml         \
   TCP3_auxFnsScript.sml        \
   TCP3_hostLTSScript.sml       \
   TCP3_streamScript.sml        \
   TCP3_netScript.sml           \
   TCP3_absFunScript.sml
SPECTHEORIES=$(patsubst %Script.sml,%,$(SPECTHEORYFILES))
SPECTHEORYIMNS=$(addsuffix .imn, $(SPECTHEORIES))
SPECTHEORYPSFILES=$(addsuffix -doc.ps, $(SPECTHEORIES))
SPECTHEORYPDFFILES=$(addsuffix -doc.pdf, $(SPECTHEORIES))

SPECOTHERPUBLICFILES=\
  Holmakefile \
  fmapUtilsScript.sml

# SPECOTHERPUBLICFILES=\
#   Net_Hol_reln.sig \
#   Net_Hol_reln.sml \
#   Version.sig      \
#   Phase.sig        \
#  Phase.sml

SPECPUBLICFILES=$(SPECTHEORYFILES) $(SPECOTHERPUBLICFILES)


tarball-spec-public.tar.gz:
	rm -rf tarball-spec-public*
	mkdir tarball-spec-public
	mkdir tarball-spec-public/Spec3
	cp $(SPECPUBLICFILES) tarball-spec-public/Spec3
	cvs status $(SPECPUBLICFILES) > tarball-spec-public/Spec3/VERSIONS-spec-public
	cp ../doc/README-spec-public tarball-spec-public/Spec3
	cp ../doc/LICENSE-spec-public tarball-spec-public/Spec3
	tar -cvf tarball-spec-public.tar tarball-spec-public
	gzip tarball-spec-public.tar

install-tarball-spec-public: tarball-spec-public.tar.gz
	cp -f tarball-spec-public.tar.gz /homes/pes20/public_html/Netsem

tarball-Spec3-public:
	rm -rf tarball-Spec3-public*
	mkdir tarball-Spec3-public
	mkdir tarball-Spec3-public/Spec3
	cp $(SPECPUBLICFILES) tarball-Spec3-public/Spec3
	cvs status $(SPECPUBLICFILES) > tarball-Spec3-public/Spec3/VERSIONS-Spec3-public


# list of source files for the checker.  This is just used for the wc (and is a guess)

# list of source files for the checker.  This is just used for the wc (and is a guess)
CHECKERSOURCEFILES = \
  NetEvalScript.sml \
  Net_fmap_analyse.sml  \
  TCP1_bettersScript.sml \
  TCP1_boundsInference.sml \
  TCP1_timerPropsScript.sml \
  TCP1_seq32PropsScript.sml \
  Evaluator.sml \
  CheckTraces.sml

HOLTHEORIES=$(patsubst %Script.sml,%,$(wildcard *Script.sml))

# Theories that don't generate .imn files:
NONIMNTHEORIES=integer_word32 LetCompute

HOLTHEORYIMNS=$(addsuffix .imn, $(filter-out $(NONIMNTHEORIES), $(HOLTHEORIES)))

# hack to generate brief table of contents
BRIEFTOC='Contents|Index|{chapter}|{bchy}|deliver\\|timer\\_tt'


#
# hack from GNU Make manual, to set $(space) to a single space:
#
nullstring :=
space := $(nullstring) # end of the line

# main targets:

all:
	@echo "This is a dummy Makefile.  Use Holmake to build HOL scripts."
	@echo ""
	@echo "Use \`make doc' to build documentation (host LTS only),"
	@echo "  or \`make alldoc' to build documentation for all HOL scripts."
	@echo ""
	@echo "Do \`make FAST=1 doc' to ignore dependencies on HOL-derived files."
	@echo "Do \`make BLACK=1 doc' to force unknown vars to appear in black anyway."
	@echo "  (or tinydoc/alltinydoc for small version)"
	@echo ""
	@echo "Use \`Holmake --fast' to build the HOL stuff."
	@echo ""
	@echo "Other targets: v, again, clean, realclean, prog, stealimn."
	@echo ""
	@echo "Or, for any fooScript.sml, make foo-doc.ps or foo-tinydoc.ps."
	@echo "or make alldoc / make alltinydoc to make the lot of them."

doc: TCP3_hostLTS-doc.ps TCP3_hostLTS-doc.pdf # glossary.ps
     #TCP3_netLTS-doc.ps

tinydoc: TCP3_hostLTS-tinydoc.ps

doc-for-streamspec:
	make BLACK=1 alldoc-inc.tex

alldoc: alldoc.ps alldoc.pdf

alldoc-old: $(SPECTHEORYPSFILES) $(SPECTHEORYPDFFILES)
alltinydoc: $(addsuffix -tinydoc.ps, $(SPECTHEORIES))

installalldoc : alldoc-old alldoc
	cp -f alldoc.ps alldoc.pdf $(SPECTHEORYPSFILES) $(SPECTHEORYPDFFILES) /home/pes20/public_html/PEPITO/WP1/TCP

install-www-internal : alldoc-old alldoc
	cp -f alldoc.ps alldoc.pdf $(SPECTHEORYPSFILES) $(SPECTHEORYPDFFILES) /usr/groups/tthee/www-internal

install-draft : alldoc.ps alldoc.pdf
	cp -f alldoc.ps /homes/pes20/public_html/Netsem/TCP-draft
	cp -f alldoc.pdf /homes/pes20/public_html/Netsem/TCP-draft

install : alldoc.ps alldoc.pdf alldoc2up.ps
	cp -f alldoc2up.ps /home/pes20/public_html/Netsem/
	cp -f alldoc.ps /home/pes20/public_html/Netsem/
	cp -f alldoc.pdf /home/pes20/public_html/Netsem/

alldoc2up.ps : alldoc.ps
	psnup -2up alldoc.ps alldoc2up.ps

stealimn :
	cp -a /usr/groups/tthee/local/Net/TCP/Spec1/*.imn .

v: doc
	ghostview TCP3_hostLTS-doc.ps &
#	ghostview TCP3_netLTS-doc.ps &

again:
	rm -f *-doc.{ps,dvi}

tinyagain:
	rm -f *-tinydoc.{ps,dvi}

clean:
	rm -f *-{tiny,}doc.{ps,tex,log,toc,pdf} *.tmp-tex *.errs *.dvi TCP3_auto.imn *.aux *.tmp2-tex *.tmp3-tex alldoc{,-c}.{ps,tex,log,toc,pdf,idx,ilg,ind,tob}

realclean: clean
	rm -rf $(HOLTHEORYIMNS)

prog:
	cd ${HOLDOCDIR}; make lts_to_latex

.PHONY: all doc v clean realclean prog


# document targets:

%.tmp-tex : %Script.sml $(if ${FAST},,${IMNFILES}) ${LTS_TO_LATEX}
	$(LTS_TO_LATEX) $(EXTRAIMNFILES) $(IMNFILES) $< > $@

%.tmp2-tex : %Script.sml $(if ${FAST},,${IMNFILES}) ${LTS_TO_LATEX}
	$(LTS_TO_LATEX) -nocmds $(EXTRAIMNFILES) $(IMNFILES) $< > $@

%.tmp3-tex : %Script.sml $(if ${FAST},,${IMNFILES}) ${LTS_TO_LATEX}
	$(LTS_TO_LATEX) -cmds -nomerge $(EXTRAIMNFILES) $(IMNFILES) $< > $@

%-doc.tex : %.tmp-tex doc-pre.template $(if ${BLACK},doc-black.template,) doc-post.template
	echo "% auto-generated file; do not edit" | \
        cat - doc-pre.template $(if ${BLACK},doc-black.template,) $< doc-post.template > $@

%-tinydoc.tex : %.tmp-tex tinydoc-pre.template $(if ${BLACK},doc-black.template,) doc-post.template
	echo "% auto-generated file; do not edit" | \
        cat - tinydoc-pre.template $(if ${BLACK},doc-black.template,) $< doc-post.template > $@
# other targets:

# N.B. also depends on other things in stream_spec
alldoc.tex : alldoc-pre.template alldoc-between.template alldoc-post.template $(addsuffix .tmp2-tex, $(SPECTHEORIES)) stream_spec/stream_spec.mng
	-cd stream_spec && make stream_spec.tex
	(echo "% auto-generated file; do not edit"; \
	cat alldoc-pre.template; \
	for f in $(SPECTHEORIES); do \
		g=`echo $$f | sed -e 's/_/\\\\\\\\protect\\\\\\\\textunderscore /g'`; \
		cat alldoc-between.template | sed -e "s/THEORYNAME/$$g/g"; \
		cat $$f.tmp2-tex; \
	done; \
	cat alldoc-post.template \
	) > $@
	sed -i -e 's/\$$Id/\$$ Id/g' $@ # protect rcsid if subsequently commit alldoc.tex

alldoc-c.tex : alldoc-c-pre.template alldoc-c-between.template alldoc-c-post.template $(addsuffix .tmp-tex, $(SPECTHEORIES))
	(echo "% auto-generated file; do not edit"; \
	cat alldoc-c-pre.template; \
	for f in $(SPECTHEORIES); do \
		g=`echo $$f | sed -e 's/_/\\\\\\\\protect\\\\\\\\textunderscore /g'`; \
		cat alldoc-c-between.template | sed -e "s/THEORYNAME/$$g/g"; \
		cat $$f.tmp-tex; \
	done; \
	cat alldoc-c-post.template \
	) > $@

alldoc-inc.tex : alldoc-inc-pre.template alldoc-inc-between.template alldoc-inc-post.template $(addsuffix .tmp3-tex, $(SPECTHEORIES))
	(echo "% auto-generated file; do not edit"; \
	cat alldoc-inc-pre.template; \
	for f in $(SPECTHEORIES); do \
		g=`echo $$f | sed -e 's/_/\\\\\\\\protect\\\\\\\\textunderscore /g'`; \
		cat alldoc-inc-between.template | sed -e "s/THEORYNAME/$$g/g"; \
		cat $$f.tmp3-tex; \
	done; \
	cat alldoc-inc-post.template \
	) > $@

alldoc-inc.dvi : alldoc-inc.tex
	@echo
	@echo "Sorry, you can't build alldoc-inc directly; you must include it in another document"
	@exit 1

TCP3_auto.imn: $(SPECTHEORYIMNS)
	echo '(*[ NOECHO ]*)' > $@
	cat $(filter-out %LIBinterface.imn %ruleids.imn, $(SPECTHEORYIMNS)) >> $@
	echo '(*[ CLASS RULE "\tsrule" ]*)' >> $@
	echo '(*[ ECHO ]*)' >> $@

#
# re-create user configuration if missing:
#

munge.mk :
	@echo ''
	@echo Re-creating $@...
	@tail -n+2 munge.mk.in > $@
	@echo Now run make again.
	@echo ''


# implicit rules:

.PRECIOUS: %.tmp-tex %-doc.tex %.dvi %.tob


#this was also a rule for the .pdf, but pdflatex runs out of space here
alldoc.dvi : alldoc.tex $(LTSHOLDOCDIR)/ltsmunge.sty $(OTHERTEXFILES)
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
	-makeindex alldoc
	BIBINPUTS=$(subst $(space),:,$(strip $(EXTRABIBINPUTS))):$(TEXINPUTS) bibtex alldoc
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
#	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(PDFLATEX) alldoc.tex


# alldoc.pdf : alldoc.tex $(LTSHOLDOCDIR)/ltsmunge.sty $(OTHERTEXFILES)
# 	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
# 	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
# 	-makeindex alldoc
# 	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
# 	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
# 	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(PDFLATEX) alldoc.tex

# now go via ps to avoid problem with eps figures from stream_spec
alldoc.pdf : alldoc.ps
	ps2pdf alldoc.ps

alldoc-quick : alldoc.tex $(LTSHOLDOCDIR)/ltsmunge.sty $(OTHERTEXFILES)
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) alldoc.tex
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(DVIPS) $(DVIPSFLAGS) alldoc.dvi -o alldoc.ps.tmp
	mv alldoc.ps.tmp alldoc.ps

alldoc-pquick : alldoc.tex $(LTSHOLDOCDIR)/ltsmunge.sty $(OTHERTEXFILES)
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(PDFLATEX) alldoc.tex
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob
	-makeindex alldoc

brieftoc : alldoc.toc   #for testing purposes
	grep -E $(BRIEFTOC) alldoc.toc > alldoc.tob


%.dvi %.pdf : %.tex $(LTSHOLDOCDIR)/ltsmunge.sty $(OTHERTEXFILES)
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) $<
	-makeindex $*
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(LATEX) $<
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(PDFLATEX) $<

%-tinydoc.ps : %-tinydoc.dvi
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(DVIPS) -y 500 -O -0.5in,-0.5in $< -o $@

%.tex : %.mng $(if ${FAST},,${IMNFILES}) ${MNG_TO_LATEX}
	  $(MNG_TO_LATEX) $(IMNFILES) $*.mng > $*.tex

%.ps : %.dvi
	TEXINPUTS=$(subst $(space),:,$(strip $(EXTRATEXINPUTS))):$(TEXINPUTS) $(DVIPS) $(DVIPSFLAGS) $< -o $@.tmp
	mv $@.tmp $@

%.pdf : %.ps
	$(PSTOPDF) $< $@.tmp
	mv $@.tmp $@

wc:
	wc -l -c   $(SPECTHEORYFILES)
	wc -l -c   $(CHECKERSOURCEFILES)

glomspec:
	cat $(SPECTHEORYFILES) > TCP3_SPECTHEORYFILES.txt


archdiffs:
	egrep -n "linux_arch|bsd_arch|windows_arch|unix_arch" *Script.sml |wc

todo:
	@echo "TODO1/2 - issues that must be fixed"
	@echo "TODO1 - doc issues"
	@grep "TODO1" $(SPECTHEORYFILES) | wc -l
	@echo "TODO2 - semantic issues"
	@grep "TODO2" $(SPECTHEORYFILES) | wc -l
	@echo "TODO3 - whole descriptions that need to be written"
	@grep "TODO3" $(SPECTHEORYFILES) | wc -l
	@echo "TODO5 - typesetting and reference issues "
	@grep "TODO5" $(SPECTHEORYFILES) | wc -l

# extra dependencies:

%-doc.dvi : $(LTSHOLDOCDIR)/ltsmunge.sty tcp.sty

# end

# # TCP1 files that we need to link
# # this is sometimes helpful when we want Holmake to treat Spec1 and Spec3 as a combined spec e.g. for dependency information
# TCP1_FILES=Chaining.sig \
# Chaining.sml \
# CheckTraces.sml \
# Evaluator.sml \
# GroundTrace.sig \
# GroundTrace.sml \
# GroundTraceMain.sml \
# Holmakefile \
# LetComputeLib.sig \
# LetComputeLib.sml \
# LetComputeScript.sml \
# MANIFEST \
# Makefile \
# NetEvalScript.sml \
# Net_Hol_reln.sig \
# Net_Hol_reln.sml \
# Net_fmap_analyse.sig \
# Net_fmap_analyse.sml \
# Phase.sig \
# Phase.sml \
# README.testing \
# TCP1_.imn \
# TCP1_LIBinterfaceScript.sml \
# TCP1_auxFnsScript.sml \
# TCP1_baseTypesScript.sml \
# TCP1_bettersScript.sml \
# TCP1_boundsInference.sml \
# TCP1_errorsScript.sml \
# TCP1_evalSupportScript.sml \
# TCP1_host0Script.sml \
# TCP1_hostLTSScript.sml \
# TCP1_hostTypesScript.sml \
# TCP1_net1Script.sml \
# TCP1_net1_to_netScript.sml \
# TCP1_netScript.sml \
# TCP1_netTypesScript.sml \
# TCP1_paramsScript.sml \
# TCP1_preHostTypesScript.sml \
# TCP1_rangeAnalysisScript.sml \
# TCP1_ruleidsScript.sml \
# TCP1_seq32PropsScript.sml \
# TCP1_signalsScript.sml \
# TCP1_timerPropsScript.sml \
# TCP1_timersScript.sml \
# TCP1_urgencyScript.sml \
# TCP1_utilPropsScript.sml \
# TCP1_utilsScript.sml \
# TraceFiles.sml \
# Version.sig \
# Version.sml \
# alldoc-between.template \
# alldoc-c-between.template \
# alldoc-c-post.template \
# alldoc-c-pre.template \
# alldoc-inc-between.template \
# alldoc-inc-post.template \
# alldoc-inc-pre.template \
# alldoc-post.template \
# alldoc-pre.template \
# doc-black.template \
# doc-inplace-post.template \
# doc-inplace-pre.template \
# doc-post.template \
# doc-pre.template \
# driveNet.sml \
# errata.txt \
# find_int_inst.sig \
# find_int_inst.sml \
# genstrings.sml \
# glossary.mng \
# ground_tickers.sig \
# ground_tickers.sml \
# hosthistory.xls \
# html_header \
# html_trailer \
# ifpdf.sty \
# incdemo.tex \
# inetheaders.inc \
# integer_word32Script.sml \
# interactive-checking \
# invariants.txt \
# munge.mk.in \
# nocomment.imn \
# numrelnorm.sig \
# numrelnorm.sml \
# order_calc \
# position.txt \
# quant-check.ml \
# rationale.txt \
# rules.txt \
# tcp.sty \
# testEval.sml \
# testEval_utils.sml \
# tinydoc-pre.template \
# trace_checker.sml

# TCP1_FILES: $(TCP1_FILES)

# $(TCP1_FILES):
# 	@#@-rm $@ 2>&1 >>/dev/null
# 	ln -s ../Spec1/$@ $@

# cleanTCP1_FILES:
# 	-rm $(TCP1_FILES)
