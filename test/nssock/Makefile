CC=cc
CCOPTS=-c -Wall -DNDEBUG -fPIC
MKDEP=$(CC) -M
MKLIB=ar
MKLIBOPTS=-q

OFILES=ns_aux.o ns_errors.o ns_sockets.o
LIBOUT=libnssock.a

all: libnssock.a

libnssock.a: $(OFILES)
	$(MKLIB) $(MKLIBOPTS) $(LIBOUT) $(OFILES)

depend:
	$(MKDEP) *.c > .depend

clean:
	rm -f *.[oa]

realclean: clean
	rm -f .depend

.SUFFIXES: .c .o

.c.o:
	$(CC) $(CCOPTS) $<

-include .depend
