CC=cc
MKLIB=ar
NSSOCKPATH=../nssock/
NSSOCKLIB=nssock
NTPLIB=ntpspoof

OSTYPE=$(shell uname -o)

all: sockpreload.so

libntpspoof.a:
	$(CC) -c ntp_spoof.c
	$(MKLIB) -r $@ ntp_spoof.o

sockpreload.so: libntpspoof.a socket_preload.c ../nssock/libnssock.a
	if [ $(OSTYPE) = "FreeBSD" ]; then \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L. -o sockpreload.so \
	-shared -static socket_preload.c -l$(NSSOCKLIB) \
	-lntpspoof
	else \
	$(CC) -I $(NSSOCKPATH) -L $(NSSOCKPATH) -L. -o sockpreload.so \
	-shared -static socket_preload.c -l$(NSSOCKLIB) \
	-lntpspoof -ldl
	fi

clean:
	rm -f *.o sockpreload.so

realclean: clean

depend:
