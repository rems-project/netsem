/* hotgzip - a gzip filter that flushes all output as soon as it receives it. */

/* Keith Wansbrough, 2004-02-20.. */

/* uses zlib, a.k.a. libz */

/* no options */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include "zlib.h"

int main(int argc, char *argv[]) {
  int n;
  char buf[65536];
  gzFile f;
  int ofd;

  if ((ofd = dup(STDOUT_FILENO)) < 0) {
    perror(argv[0]);
    exit(3);
  }

  if (! (f = gzdopen(ofd, "wb"))) {
    fprintf(stderr,"%s: couldn't gzdopen\n",argv[0]);
    exit(4);
  }

  while (0 != (n = read(STDIN_FILENO, buf, sizeof(buf)))) {
    if (n < 0) {
      if (errno != EINTR) {
        perror(argv[0]);
        exit(1);
      }
    } else {
      int m;
      char *p = buf;
      while (n > 0) {
        m = gzwrite(f, p, n);
        if (m <= 0) {
          fprintf(stderr,"%s: couldn't gzwrite\n",argv[0]);
          exit(2);
        } else {
          p += m;
          n -= m;
        }
      }
      gzflush(f, Z_SYNC_FLUSH);
    }
  }

  if (gzclose(f) != 0) {
    fprintf(stderr,"%s: gzclose error\n",argv[0]);
  }

  exit(0);
}
