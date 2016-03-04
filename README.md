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
