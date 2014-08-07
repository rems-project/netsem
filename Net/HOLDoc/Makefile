# First build HOL/tools/holdoc from the HOL repository. The following
# var should point to HOL/tools/holdoc. Probably easiest to run make
# as
#
# make HOLDOCDIR=/path/to/my/HOL/tools/holdoc
#
# after all, we don't expect to build it that often.
#
# Another comment is that Out_of_memory errors for ocaml executables
# can be fixed by using OCAMLPARAM with the h flag
#
HOLDOCDIR=FIXME

OCAMLC=  ocamlc
OCAMLOPT=ocamlopt
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc
OCAMLDEP=ocamldep -native

OCAMLFLAGS=-I $(HOLDOCDIR)

LATEX=latex
DVIPS=dvips

# holdoc.mk is generated from holdoc.mk.in, so your local
# changes to holdoc.mk won't accidentally go into CVS
# include holdoc.mk
# files:

MLSOURCES=lts_to_latex.ml
MLISOURCES=
OTHERSOURCES=
GENMLSOURCES=
GENMLISOURCES=

HOLDOCBASEFILES=holdocmodel holdoc_init holparsesupp hollex holparse simpledump holparsetools mngdump
HOLDOCFILES=$(addsuffix .cmx, $(addprefix $(HOLDOCDIR)/, $(HOLDOCBASEFILES)))

# main target:

all: lts_to_latex

# program targets:

lts_to_latex : $(HOLDOCFILES) lts_to_latex.cmx
	$(OCAMLOPT) $(OCAMLFLAGS) str.cmxa $+ -o $@

# document targets:

Net_hostLTSScript.tex : ../HOL-model/Net_hostLTSScript.sml lts_to_latex
	cat ../HOL-model/Net.imn $< | ./lts_to_latex 2>&1 > $@ \
		| sort | uniq -c | tee Net_hostLTSScript.errs

hostlts.dvi : hostlts.tex Net_hostLTSScript.tex ltsmunge.sty
	latex hostlts.tex

# other targets:

clean:
	rm -f lts_to_latex $(GENMLSOURCES) $(GENMLISOURCES) \
	      *.cm[iox] *.cmxa *~ '#*#' \
	      *.o \
              .depend Net_hostLTSScript.tex hostlts.{dvi,ps} \
              *.{aux,log}

depend:	.depend

#
# re-create user configuration if missing:
#
# holdoc.mk :
# 	@echo ''
# 	@echo Re-creating $@ from template...
# 	@grep -v "^##" holdoc.mk.in > $@
# 	@echo You may need to run make again.
# 	@echo ''
# 	@echo 'Please ignore the following "Error 42":'
# 	@exit 42  # force abort of make


# implicit rules:

%.cmx : %.ml %.cmi
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

%.cmi : %.mli
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

%.dvi : %.tex
	$(LATEX) $<

%.ps : %.dvi
	$(DVIPS) $< -o $@

# this one must come *after* the individual .cmx / .cmi rules:
%.cmx %.cmi : %.ml
	$(OCAMLOPT) $(OCAMLFLAGS) -c $<

%.ml : %.mll
	$(OCAMLLEX) $<

%.mli %.ml : %.mly
	$(OCAMLYACC) -v $<

# extra dependencies:

# weirdly, OCaml-3.06 ocamldep can't handle .mll files!
# - and even if I include $(GENMLSOURCES) $(GENMLISOURCES), these are handled wrongly.
.depend: $(MLSOURCES) $(MLISOURCES) $(GENMLSOURCES) $(GENMLISOURCES)
	$(OCAMLDEP) $(MLSOURCES) $(MLISOURCES) $(GENMLSOURCES) $(GENMLISOURCES) > $@

-include .depend

# end

