/* hotgunzip - a gunzip filter that flushes all output as soon as it receives it. */

/* Keith Wansbrough, 2004-02-20.. */

/* uses zlib, a.k.a. libz */

/* no options */

/* gargh, not really gzip... */

/* unlike for compression, there's no way to insist to zlib's gz*
   layer that it should give the output as soon as it can.  So we have
   to use the next-lower API level. :-( */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <assert.h>
#include "zlib.h"

int main(int argc, char *argv[]) {
  int n;
  char ibuf[65536];
  char obuf[65536];
  gzFile f;
  int ifd;
  z_stream strm;
  int nomore;
  int should_be_done;
  int r;
  char *p;

  /* set up strm */
  strm.next_in = ibuf;
  strm.avail_in = 0;
  strm.next_out = 0;
  strm.avail_out = 0;
  strm.zalloc = Z_NULL;
  strm.zfree = Z_NULL;
  strm.opaque = 0;

  /* initialisation: read gzip header, fake zlib header, and pass it in */
  n = 10;
  p = ibuf;
  while (n > 0) {
    r = read(STDIN_FILENO, p, n);
    if (r == 0) {
      fprintf(stderr,"%s: unexpected EOF in header\n",argv[0]);
      exit(8);
    } else if (r < 0) {
      perror(argv[0]);
      exit(9);
    }
    n -= r;
    p += r;
  }
  if (ibuf[0] != '\x1F' || ibuf[1] != '\x8B') {
    fprintf(stderr,"%s: file format error in header\n",argv[0]);
    exit(10);
  }
  if (ibuf[2] != 8 || (ibuf[3] & ~1) != 0) {
    fprintf(stderr,"%s: unimplemented header options\n",argv[0]);
  }
  ibuf[0] = 8;
  ibuf[1] = 29;
  strm.next_in = ibuf;
  strm.avail_in = 2;
  r = inflateInit(&strm);
  if (r != Z_OK) {
    fprintf(stderr,"%s: inflateInit error %d: %s\n",argv[0],r,strm.msg);
    exit(3);
  }
  r = inflate(&strm,Z_SYNC_FLUSH);  /* move next_in pointer past header */
  if (r != Z_OK) {
    fprintf(stderr,"%s: initial inflate error %d: %s\n",argv[0],r,strm.msg);
    exit(11);
  }
  strm.next_in = ibuf + 2;

  /* main loop */
  nomore = 0;
  should_be_done = 0;
  do {
    int remain;
    assert(strm.avail_in == 0 || should_be_done);  /* inflate should have used it all */
    remain = (ibuf + sizeof(ibuf)) - (char *)strm.next_in;
    if (remain == 0) {  /* at end; wrap around */
      strm.next_in = ibuf;
      remain = sizeof(ibuf);
    }

    while ( (n = read(STDIN_FILENO, strm.next_in, remain)) < 0 && errno == EINTR);
    if (n == 0) {
      nomore = 1;
    } else if (n < 0) {
      perror(argv[0]);
      exit(1);
    }
    strm.avail_in = n;

    if (!nomore) {
      if (should_be_done) {
        fprintf(stderr,"%s: Decompression error: unexpected trailing data\n",argv[0]);
        exit(13);
      }
      do {
        strm.next_out = obuf;
        strm.avail_out = sizeof(obuf);
        r = inflate(&strm, Z_SYNC_FLUSH);
        n = (char *)strm.next_out - obuf;
        if (r == Z_DATA_ERROR && strm.avail_in == 4) {
          should_be_done = 1;
        }
        if (r != Z_OK && r != Z_STREAM_END && !should_be_done) {
          fprintf(stderr,"%s: inflate error %d: %s\n",argv[0],r,strm.msg);
          exit(4);
        }
        int m;
        char *p = obuf;
        while (n > 0) {
          m = write(STDOUT_FILENO, p, n);
          if (m <= 0) {
            if (errno != EINTR) {
              perror(argv[0]);
              exit(2);
            }
          } else {
            p += m;
            n -= m;
          }
        }
      } while (strm.avail_out == 0);

    }

  } while (!nomore);

  if ((r = inflateEnd(&strm)) != Z_OK) {
    fprintf(stderr,"%s: inflateEnd error %d: %s\n",argv[0],r,strm.msg);
    exit(5);
  }

  if (close(STDIN_FILENO) != 0) {
    perror(argv[0]);
    exit(6);
  }

  exit(0);
}
