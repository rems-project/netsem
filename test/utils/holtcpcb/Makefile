CC=gcc
CFILES=holtcpcb.c
RM=rm -f

NTPLIBDIR=../../common/
NTPLIB=ntplib

all: holtcpcb

holtcpcb: $(CFILES:.c=.o)
	$(CC) -L $(NTPLIBDIR) -o $@ $(CFILES:.c=.o) -l$(NTPLIB)

realclean: clean

clean:
	$(RM) $(CFILES:.c=.o) holtcpcb

depend:

.SUFFIXES:.c .o

.c.o:
	$(CC) -Wall -c $<

