Network Semantics
======


This repository contains the formal specification of TCP, UDP, and the Sockets API developed in the Netsem project:

http://www.cl.cam.ac.uk/~pes20/Netsem/index.html

It has been relicensed under the simplified BSD license.  Currently (2015), it
is revived using contemporary systems (newer HOL4, PolyML, dtrace, ..)


The `demo-traces/` directory contains some example traces (state is unclear)

The `HOLDoc/` directory contains tools to typeset the specification (compiles and works).

The `notes/` directory contains (meeting and other random) notes.

The `specification/` directory contains the segment-level HOL4 specification (previously called `Spec1`).

The `test/` directory contains the test generation and checking tools.

The `unmaintained/` directory contains unmaintained specifications, the [Lem](https://bitbucket.org/Peter_Sewell/lem/) port of the specifications, etc.

Building
======

- Get [PolyML](http://polyml.org) (5.5.2 works fine)
- Get [HOL](https://hol-theorem-prover.org/) (at least 3df6c6b3318ff5bb9e097003d332d06c8004ad8d from 18th Sep 2015)
- Building specification: `cd specification ; $HOL/bin/Holmake`
- Building documentation: `cd HOLDoc/src ; $HOL/bin/Holmake` followed by `cd specification ; $HOL/bin/Holmake TCP1_net1Theory.ui TCP1_netTheory.ui ; make alldoc`
- Building test tools (required OCaml (tested with 4.02.3)): `cd test ; make depend OCAMLPATH=MY_OCAML_PATH ; make OCAMLPATH=MY_OCAML_PATH`