# pull labels from check run
%.labels.mng: %.out.html
	cat $*.out.html |grep "LATEXTRANS" > $*.labels.mng

# apply poor-mans-munger to labels
%.labels.tex: %.labels.mng
	sed -e 's/\[\[/$$\\mathit{/g' -e 's/\]\]/\}$$/g' -e 's/_/\\_/g' < $*.labels.mng > $*.labels.tex

# build annotatated diagram from trace and labels
%.annotated.tex.inc %.annotated.ps.gz: % %.labels.tex
	../Test/scripts/build-diags2 $*

# build conventional zig-zag diagram from trace
%.ps.gz: %
	../Test/scripts/build-diags $*

# invert send and receive labels in aux file, working around broken test gen
inv:
	sed -e 's/senddatagram/Recvdatagram/g' -e's/recvdatagram/senddatagram/g' -e's/Recvdatagram/recvdatagram/g' < trace5000aux > trace5000aux-inv
	sed -e 's/senddatagram/Recvdatagram/g' -e's/recvdatagram/senddatagram/g' -e's/Recvdatagram/recvdatagram/g' < trace5001aux > trace5001aux-inv


# remove all the files which are generable locally (some of these may
#  be checked in, to reduce techreport dependency on tools)

reallyclean:
	rm -rf *.labels.mng *.labels.tex *.annotated.ps.gz *.annotated.tex *.annotated.tex.inc *.ps.gz

