
# munge.mk - user-specific configuration file for munging:
#

#
# Location of mng_to_latex:
#
#MNGTOLATEXDIR=/usr/groups/tthee/local/hol98/tools/holdoc
MNGTOLATEXDIR=$(HOME)/HOLDoc

HOLMNGDIR=../../HOLDoc

MNGTOLATEX=${MNGTOLATEXDIR}/mng_to_latex

#
# Path(s) to miscellaneous TeXery required
#
EXTRATEXINPUTS+=$(MNGTOLATEXDIR):$(HOLMNGDIR)

#
# Location of various standard programs:
#
# you can safely replace hugelatex with latex,
# if it's not on your system...
LATEX=hugelatex
DVIPS=dvips

