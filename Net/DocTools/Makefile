# override this by setting OCAMLPATH in your .profile; if your OCaml
# version is before 3.03a, also set OCAMLPPFLAGS to the empty string.
OCAMLPATH?=/usr/groups/netsem/ocaml/bin
OCAMLPPFLAGS?=-pp $(OCAMLPATH)/camlp4o
# add -pp camlp4o for ocaml version 3.03a and above, apparently

OCAMLC=$(OCAMLPATH)/ocamlc $(OCAMLPPFLAGS)
OCAMLLEX=$(OCAMLPATH)/ocamllex
OCAMLYACC=${OCAMLPATH}/ocamlyacc
OCAMLDEP=$(OCAMLPATH)/ocamldep $(OCAMLPPFLAGS)


# figures:

FIGURES=abstestnet testnet threadboxnet protstack chasm chasm-bridge abstestnet2 protstack2 threadboxnet2

abstestnet_FIG_OPTS=-m 0.707
testnet_FIG_OPTS=-m 0.707
# threadboxnet_FIG_OPTS=-m 0.841
threadboxnet_FIG_OPTS=-m 0.707
threadboxnet2_FIG_OPTS=-m 1.4
protstack_FIG_OPTS=-m 0.707

chasm_FIG_OPTS=-m 1.000
chasm-bridge_FIG_OPTS=-m 0.4500
abstestnet2_FIG_OPTS=-m 1.000
protstack2_FIG_OPTS=-m 1.400



FIGURE_PSTEX_TS=$(addsuffix .pstex_t, $(FIGURES))


# main target:

all: typography.dvi typography-minicaml2.dvi make-err.log wc_strip rhbeat2

rhbeat2: tmp-rhbeat2.tex tmp-rhbeat2-a.tex tmp-rhbeat2-b.tex tmp-rhbeat2-mli.tex tmp-rhbeat2-alan.tex tmp-rhbeat2-kurt.tex

tmp-rhbeat2-mli.tex : ../UDPlang/OCAML/rhbeat2.mli munge_ocaml
	( cat ../UDPlang/OCAML/rhbeat2.mli | ./munge_ocaml ) \
          > tmp-rhbeat2-mli.tex 2> err-tmp-rhebat2-mli.log


   # list here all TEX and ML files to be munged: PS removed TX  shbeat
   TEXIFY = body ocaml ocaml2 repeated-proof body-slides
   MLIFY = repeated-single-send single-send single-recv shbeat-a shbeat-b  \
           rhbeat2 rhbeat2-a rhbeat2-b rhbeat2-alan rhbeat2-kurt

   # list here the basic names of all the tmp-NAME.tex files:
   TMPFILES = rules ruledefs seq $(TEXIFY) $(MLIFY)

   # from the above we compute tmp-NAME.tex and err-NAME.log:
   TMPTEXFILES = $(addprefix tmp-, $(addsuffix .tex, $(TMPFILES)))
   TMPLOGFILES = $(addprefix err-, $(addsuffix .log, $(TMPFILES)))

   # now the main document target:

   typography.dvi : typography.tex  t1bchx.fd ../Sem/abstract.tex $(TMPTEXFILES) $(FIGURE_PSTEX_TS)
	latex typography

   typography.pdf : typography.tex  t1bchx.fd ../Sem/abstract.tex $(TMPTEXFILES) $(FIGURE_PSTEX_TS)
	pdflatex typography

   typography-slides.dvi : typography-slides.tex  t1bchx.fd  $(TMPTEXFILES) $(FIGURE_PSTEX_TS)
	latex typography-slides

   typography-slides.ps : typography-slides.dvi
	dvips typography-slides

   typography-minicaml2.dvi : typography-minicaml2.tex  t1bchx.fd ../Sem/abstract.tex $(TMPTEXFILES) $(FIGURE_PSTEX_TS)
	latex typography-minicaml2

   make-err.log : $(TMPLOGFILES)
	cat $(TMPLOGFILES) | sort | uniq > make-err.log

wc: wc_strip
	cat ../Sem/body.tex | wc_strip | wc
	cat typography.bbl | wc_strip | wc

ps: typography.dvi
	dvips  typography

# irregular parts of the document:

   tmp-rules.tex tmp-rawruledefs.tex err-rules.log : ../Sem/rules.txt rebracket rules_to_latex munge
	( cat ../Sem/rules.txt | ./rebracket | ./rules_to_latex | ./munge ) \
          > tmp-rules.tex 2> err-rules.log

   tmp-ruledefs.tex err-ruledefs.log : tmp-rawruledefs.tex munge
	( cat tmp-rawruledefs.tex | ./munge ) \
	  > tmp-ruledefs.tex 2> err-ruledefs.log

   tmp-seq.tex err-seq.log : ../Sem/seq.txt infer rebracket munge
	( cat ../Sem/seq.txt | ./infer | ./rebracket | ./munge ) \
          > tmp-seq.tex 2> err-seq.log

# program targets:

   infer : infer.cmo
	$(OCAMLC) infer.cmo  -cclib -lunix -o infer

   rules_to_latex : rules_parser.cmo rules_lexer.cmo  rules_to_latex.cmo rules_syntax.cmi
	$(OCAMLC) str.cma rules_parser.cmo rules_lexer.cmo rules_to_latex.cmo  -cclib -lunix -o rules_to_latex

   munge_ocaml : munge_ocaml.cmo munge_lexer.cmo
	$(OCAMLC) str.cma munge_lexer.cmo  munge_ocaml.cmo  -cclib -lunix -o munge_ocaml

   munge : munge.cmo munge_lexer.cmo
	$(OCAMLC) str.cma munge_lexer.cmo  munge.cmo  -cclib -lunix -o munge

   rebracket : rebracket.cmo munge_lexer.cmo
	$(OCAMLC) str.cma munge_lexer.cmo  rebracket.cmo  -cclib -lunix -o rebracket

   wc_strip : wc_strip.cmo munge_lexer.cmo
	$(OCAMLC) str.cma munge_lexer.cmo  wc_strip.cmo  -cclib -lunix -o wc_strip

clean:
	rm -f rules_lexer.ml rules_parser.ml rules_parser.mli rules_parser.output rules_to_latex munge_lexer.ml munge munge_ocaml infer rebracket wc_strip *.log *.toc *.aux *.cm[io] *~ tmp-*.tex *.pstex{,_t} '#*#'  typography.dvi *.xyc *.ind *.idx *.ilg *.bak typography.ps{,.gz,.pdf} *.ind.orig *.bbl *.blg typography-slides.dvi{,.ps}

clean2:
	rm -f rules_lexer.ml rules_parser.ml rules_parser.mli rules_parser.output rules_to_latex munge_lexer.ml munge munge_ocaml infer rebracket wc_strip *.log *.toc *.aux *.cm[io] *~ tmp-*.tex *.pstex{,_t} '#*#'  typography.dvi *.xyc *.ind *.idx *.ilg *.bak typography.ps{,.gz,.pdf} *.ind.orig  *.blg



# implicit rules:

   %.cmo : %.ml %.cmi
	$(OCAMLC) -c $<

   %.cmi : %.mli
	$(OCAMLC) -c $<

   # this one must come *after* the individual .cmo / .cmi rules:
   %.cmo %.cmi : %.ml
	$(OCAMLC) -c $<

   %.ml : %.mll
	$(OCAMLLEX) $<

   %.ml %.mli %.output : %.mly
	$(OCAMLYACC) -v $<

   %.pstex %.pstex_t : %.fig
	fig2dev -L pstex               $($*_FIG_OPTS) $< $*.pstex
	fig2dev -L pstex_t -p $*.pstex $($*_FIG_OPTS) $< | ./rebracket | ./munge > $*.pstex_t

   tmp-%.tex err-%.log : ../Sem/%.tex infer rebracket munge
	( cat ../Sem/$*.tex | ./infer | ./rebracket | ./munge ) \
          > tmp-$*.tex 2> err-$*.log

   tmp-%.tex err-%.log : ../UDPlang/OCAML/%.ml munge_ocaml
	( cat ../UDPlang/OCAML/$*.ml | ./munge_ocaml ) \
          > tmp-$*.tex 2> err-$*.log

# extra dependencies:

   rules_to_latex.cmo : rules_lexer.cmi rules_parser.cmi

   rules_lexer.cmo : rules_parser.cmi

   rules_parser.cmo : rules_syntax.cmi

   rules_parser.cmi : rules_syntax.cmi

   munge_ocaml.cmo : munge_lexer.cmi

   munge.cmo : munge_lexer.cmi

   rebracket.cmo : munge_lexer.cmi

   wc_strip.cmo : munge_lexer.cmi


# end
