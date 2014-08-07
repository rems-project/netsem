#ifndef ns_sockets_int_h
#define ns_sockets_int_h

extern char *geterrmsg(char *dest, int errcode);

#if defined(SO_ACCEPTCON) && !defined(SO_ACCEPTCONN)
#define SO_ACCEPTCONN SO_ACCEPTCON
#endif

#ifndef WIN32
extern int min(int a, int b);
#endif

extern int delimit_print(char *dest, unsigned int destsize,
			 const unsigned char *buf, size_t len);
extern void print(char *str);
extern int calc_iovec_len(struct iovec *vec, size_t iovlen);
extern void iovec_print(char *buf, unsigned int buflen,
			struct iovec *vec, size_t iovlen);
extern void iovec_printtail(char *buf, unsigned int buflen,
			    struct iovec *vec, size_t iovlen,
			    unsigned int start);
extern char *ns_getcurrenttime_first(char *dest, int size);
extern char *ns_getcurrenttime_last(char *dest, int size);

#endif
