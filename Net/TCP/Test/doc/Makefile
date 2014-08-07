# Makefile for TCP Test documentation

all :  protstack.eps tthee-arch.eps tcptest.ps

clean :
	rm -f *.{aux,log,dvi,toc} tthee-arch.eps protstack.eps tcptest.ps *~

%.eps : %.obj
	tgif -print -eps $<

%.dvi : %.tex
	latex $<

%.ps : %.dvi
	dvips -Pcmz -Pamz -j0 $<

%.eps : %.fig
	fig2dev -L eps $< $*.eps

