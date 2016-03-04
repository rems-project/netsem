CC=cc
NSSOCKPATH=../../nssock/
NSSOCKLIB=nssock
NTPLIBPATH=../../common/
NTPLIB=ntplib

SERVERC=sockserv.c
SERVEROUT=sockserv

CLIENTC=sockclient.c
CLIENTOUT=sockclient

#add -ldl on Linux
LDFLAGS=

all: build-server build-client

build-server: $(SERVERC) ../../nssock/libnssock.a ../../common/libntplib.a
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(SERVEROUT) $(SERVERC) -l$(NSSOCKLIB) -l$(NTPLIB) $(LDFLAGS)

build-client: $(CLIENTC)
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(CLIENTOUT)	$(CLIENTC) -l$(NSSOCKLIB) -l$(NTPLIB) $(LDFLAGS)

clean:
	rm -f *.o $(CLIENTOUT) $(SERVEROUT)

realclean: clean

depend:
