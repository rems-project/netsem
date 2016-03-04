OCAMLOPTS=-I $(OCAMLPATH)/../otherlibs/unix -I $(OCAMLPATH)/../otherlibs/str -I $(OCAMLPATH)/../otherlibs/threads

all: otracechecker histoplot stepgraph-rezero coverage apply filter histoplot2

clean:
	rm -f *.cmo *.cmi
	rm -f otracechecker hotgzip hotgunzip histoplot histoplot2 stepgraph-rezero coveragecount apply filter

otracechecker: otracechecker.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

test: test.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

hotgzip: hotgzip.c
	gcc $^ -lz -o $@

hotgunzip: hotgunzip.c
	gcc $^ -lz -o $@

histoplot: histoplot.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

histoplot2: histoplot2.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

stepgraph-rezero: stepgraph-rezero.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

coveragecount: coveragecount.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

apply: apply.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

filter: filter.ml
	ocamlc -g -thread $(OCAMLOPTS) str.cma unix.cma threads.cma -o $@ $^

depend:

realclean: clean
