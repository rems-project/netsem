# DTrace trace collection

This contains the DTrace script collecting the trace from a packetdrill test.

It requires a more-or-less current FreeBSD kernel (tested is r322062) with [one
patch](https://github.com/hannesm/freebsd/commit/8c34c9340a301e25eed69460f1655a213ef51f1b)
from gnn@ to copy out an mbuf chain.

The shell script `run_dtrace.sh` does some postprocessing of the DTrace output,
which is required since DTrace is not expressive enough.  The `copyoutmbuf`
function extracts a hexdump of the mbuf chain, which is then converted to a HOL
trace using `hextotrace.ml`.

The FreeBSD-CURRENT system under test should have some `sysctl` variables set:
- `net.inet.tcp.sack.enable=0` (disable sack)
- `net.inet.tcp.rfc3390=0` (initial window size, model has conditional, but dislikes it)
- `net.inet.tcp.rfc3465=0` (accurate counting)

The testsuite used is available at https://github.com/hannesm/tcp-testsuite
(netsem branch) with a slightly modified packetdrill (TODO: find the
modifications and put this online).
