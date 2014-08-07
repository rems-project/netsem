CC=gcc

all: logger tlogger

logger: logger.c
	$(CC) -o $@ logger.c

tlogger: tlogger.c
	$(CC) -o $@ tlogger.c

clean:
	rm -f *.o logger tlogger

realclean: clean

depend: