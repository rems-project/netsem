CC=cc
CFILES=holtcpcb-v8.c
RM=rm -f

NTPLIBDIR=../../common/
NTPLIB=ntplib

all: holtcpcb-v8

holtcpcb-v8: $(CFILES:.c=.o)
	$(CC) -L $(NTPLIBDIR) -o $@ $(CFILES:.c=.o) -l$(NTPLIB)

clean:
	$(RM) $(CFILES:.c=.o) holtcpcb

realclean: clean

depend:

.SUFFIXES:.c .o

.c.o:
	$(CC) -Wall -c $<

