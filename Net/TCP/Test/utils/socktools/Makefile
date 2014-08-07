CC=gcc
NSSOCKPATH=../../nssock/
NSSOCKLIB=nssock
NTPLIBPATH=../../common/
NTPLIB=ntplib

SERVERC=sockserv.c
SERVEROUT=sockserv

CLIENTC=sockclient.c
CLIENTOUT=sockclient

all: build-server build-client

build-server: $(SERVERC) ../../nssock/libnssock.a ../../common/libntplib.a
	if [ $(OSTYPE) = "freebsd4.6" ]; then \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(SERVEROUT) $(SERVERC) -l$(NSSOCKLIB) -l$(NTPLIB);\
	else \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(SERVEROUT) $(SERVERC) -l$(NSSOCKLIB) -l$(NTPLIB) -ldl;\
	fi

build-client: $(CLIENTC)
	if [ $(OSTYPE) = "freebsd4.6" ]; then \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(CLIENTOUT)	$(CLIENTC) -l$(NSSOCKLIB) -l$(NTPLIB);\
	else \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L $(NTPLIBPATH) \
		-o $(CLIENTOUT)	$(CLIENTC) -l$(NSSOCKLIB) -l$(NTPLIB) -ldl;\
	fi

clean:
	rm -f *.o $(CLIENTOUT) $(SERVEROUT)

realclean: clean

depend:
