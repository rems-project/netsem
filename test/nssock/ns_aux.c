#include "ns_sockets.h"
#include "ns_sockets_int.h"

#ifndef WIN32
struct timeval tval;
struct timezone tzone;
#else
#include "tsctime/TSCtime.h"
#endif

unsigned long render_number=0;

/* ---------------------------------------- */
/* int delimit_print(char *dest, unsigned ...)
 * Arguments: dest - destination string ptr
 *            destsize - size of dest buffer
 *            buf - data to delimit
 *            len - length of data to delimit
 * Returns:   0 OK, -1 error occured
 * Desc:      Produces a C-style delimited
 *            string from a buffer
 */
int delimit_print(char *dest, unsigned int destsize,
				  const unsigned char *buf, size_t len)
{
  unsigned int actlen = 0, j, i;
  char temp[6];
  temp[0] = '\0';

  if(len == 0) {
    dest[0] = (char)NULL;
    return 0;
  }

  for(i=0; i<len; i++) {
    if((buf[i] >= 32) && (buf[i] <= 127)) {
      if(actlen == (destsize - 1)) {
	dest[actlen] = (char)NULL;
	print(dest);
	actlen = 0;
      }
      dest[actlen] = (char)buf[i];
      actlen++;
    } else {
      if((actlen + 5) >= (destsize - 1)) {
	dest[actlen] = (char)NULL;
	print(dest);
	actlen = 0;
      }
      sprintf(temp, "\\x%3.3x", buf[i]);
      for(j=0; j<strlen(temp); j++) {
	dest[actlen+j] = (char)temp[j];
      }
      actlen += (unsigned int)strlen(temp);
    }
  }

  dest[actlen] = (char)NULL;
  print(dest);

  return 0;
}


#ifndef WIN32
/* ---------------------------------------- */
/* int calc_iovec_len(struct iovec *vec, ...)
 * Arguments: vec - an iovector
 *			  iovlen - lenght of vec
 * Returns:   length of iovec
 * Desc:      Calculates the length of an iovec
 */
int calc_iovec_len(struct iovec *vec, size_t iovlen)
{
  int len = 0, i;

  for(i=0; i<iovlen; i++) {
    len += vec[i].iov_len;
  }

  return len;
}


/* ---------------------------------------- */
/* void iovec_print(char *buf, ...)
 * Arguments: buf - destination buffer
 *            buflen - size of dest buffer
 *            vec - iovector to print
 *            iovlen - length of iovector
 * Returns:   void
 * Desc:      Prints an iovector as a string
 *			  (delimiting all non-printable
 *			  characters)
 */
void iovec_print(char *buf, unsigned int buflen,
		 struct iovec *vec, size_t iovlen)
{
  int i;

  for(i=0; i<iovlen; i++) {
    delimit_print(buf, buflen, vec[i].iov_base, vec[i].iov_len);
  }
}

/* ---------------------------------------- */
/* void iovec_printtail(char *buf, ...)
 * Arguments: buf - destination buffer
 *            buflen - size of dest buffer
 *            vec - iovector to print
 *            iovlen - length of iovector
 *			  start - position to print from
 * Returns:   void
 * Desc:      Prints the tail of an iovector
 *			  starting at position `start`.
 *			  This function is used by sendmsg
 *			  to print the tail of the send
 *			  buffer (i.e., the data not
 *			  successfully send).
 */
void iovec_printtail(char *buf, unsigned int buflen,
		     struct iovec *vec, size_t iovlen,
		     unsigned int start)
{
  int i, first = 1;
  unsigned int possofar = 0;

  for(i=0; i<iovlen; i++) {
    if(start <= (possofar + vec[i].iov_len)) {
      if(first == 1) {
	delimit_print(buf, buflen, vec[i].iov_base + (start-possofar),
		      vec[i].iov_len - (start-possofar));
	first = 0;
      } else
	delimit_print(buf, buflen, vec[i].iov_base, vec[i].iov_len);
    }

    possofar += vec[i].iov_len;
  }
}
#endif


/* ---------------------------------------- */
/* char *ns_getcurrenttime(char *dest, int size)
 * Arguments: dest - destination string ptr
 *            size - size of dest buffer
 * Returns:   ptr to destination string
 * Desc:      Gets the current system time
 *			  (to high accuracy) and returns
 *			  it as a string.
 */
char *ns_getcurrenttime_first(char *dest, int size)
{
  char str[LARGESTR];

#ifndef WIN32
  if(gettimeofday(&tval, &tzone) != 0) {
    sprintf(str, "(* Warning: gettimeofday failed. Next time may not be accurate! *)\n");
    print(str);
  }
  sprintf(str, "(** %lu.%6.6lu \"ns%lu\" **) ", tval.tv_sec, tval.tv_usec, render_number++);
  memcpy(dest, str, (size < strlen(str)) ? size : strlen(str));
#else
  ULONGLONG now = gethectonanotime_first() - UNIX_EPOCH;
  sprintf(str, "(** %I64u.%06I64u \"ns%lu\" **) ", now/10000000uI64, (now%10000000uI64)/10uI64, render_number++);
  memcpy(dest, str, ((unsigned)size < strlen(str)) ? size : strlen(str));
#endif

  return dest;
}


char *ns_getcurrenttime_last(char *dest, int size)
{
  char str[LARGESTR];

#ifndef WIN32
  if(gettimeofday(&tval, &tzone) != 0) {
    sprintf(str, "(* Warning: gettimeofday failed. Next time may not be accurate! *)\n");
    print(str);
  }
  sprintf(str, "(** %lu.%6.6lu \"ns%lu\" **) ", tval.tv_sec, tval.tv_usec, render_number++);
  memcpy(dest, str, (size < strlen(str)) ? size : strlen(str));
#else
  ULONGLONG now = gethectonanotime_last() - UNIX_EPOCH;
  sprintf(str, "(** %I64u.%06I64u \"ns%lu\" **) ", now/10000000uI64, (now%10000000uI64)/10uI64, render_number++);
  memcpy(dest, str, ((unsigned)size < strlen(str)) ? size : strlen(str));
#endif

  return dest;
}
