#include "../nssock/ns_sockets.h"

/* ---------------------------------------- */
/* int delimit_str(char *dest, unsigned ...)
 * Arguments: dest - destination string ptr
 *            destsize - size of dest buffer
 *            buf - data to delimit
 *            len - length of data to delimit
 * Returns:   0 OK, -1 error occured
 * Desc:      Produces a C-style delimited
 *            string from a buffer
 */
char *delimit_str(char *dest, unsigned int destsize,
		  const unsigned char *buf, size_t len)
{
  unsigned int actlen = 0, i, j;
  char temp[6];

  if(len == 0) {
    dest[0] = (char)NULL;
    return 0;
  }

  for(i=0; i<len; i++) {
    if((buf[i] >= 32) && (buf[i] <= 127)) {
      if(actlen == (destsize - 1)) {
	dest[actlen] = (char)NULL;
	return dest;
      }
      dest[actlen] = (char)buf[i];
      actlen++;
    } else {
      if((actlen + 5) >= (destsize - 1)) {
	dest[actlen] = (char)NULL;
	return dest;
      }
      sprintf(temp, "\\x%3.3x", buf[i]);
      for(j=0; j<strlen(temp); j++) {
	dest[actlen+j] = (char)temp[j];
      }
      actlen += strlen(temp);
    }
  }

  dest[actlen] = (char)NULL;
  return dest;
}




