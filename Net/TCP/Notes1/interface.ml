(*
We have to define the sockets interface that we're working with, and
explain its relationship to the POSIX/linux/BSD/... calls.

Here, I've got quickly through the POSIX spec, available at
http://www.opengroup.org/onlinepubs/007904975/idx/networking.html,
and started on an OCaml binding for everything that looks important.

We should diff also with the existing OCaml socket binding:
http://caml.inria.fr/ocaml/htmlman/libref/Unix.html

Choose:
- want a purely-functional interface, ie no passing of pointers or mutable
   values.  Are using OCaml (mutable) strings, however.  Not sure what
   to do about them - could wrap them up in an immutabliser?
- just TCP
- just IPv4
- names of types and constants to correspond -- where natural -- to
   those in POSIX
- ...but keep our ip option, port option stuff
- ...and make things abstract where sensible, eg fd instead of int.
- for now, using OCaml types (but will want HOL types too)
*)

type fd     
type ip     
type port   
type error =   EACCES | EADDRINUSE | EADDRNOTAVAIL | EAGAIN | EBADF 
             | ECONNREFUSED | EHOSTUNREACH | EINTR | EINVAL | EMFILE 
             | EMSGSIZE | ENFILE | ENOBUFS | ENOMEM | ENOTCONN      
             | ENOTSOCK 
type netmask
type ifid
type sockopt = (* SO_BSDCOMPAT | *)  SO_REUSEADDR
type tid
type 'a lift   = Star | Lift of 'a
type 'a err    = OK of 'a | Fail of error
type 'a except = EOK of 'a | EEX of exn
type void

(* could introduce a type sockaddr  = ip option * port option, to
match POSIX a bit closer. Not sure if this is a good idea. *)

exception UDP of error





%%%%%%%%%%%%%%%%%%%%%%%%


Here are the POSIX sockets interfaces, with some annotation saying
which we need to include.

The *restrict stuff in POSIX C prototypes is explained at
http://www.lysator.liu.se/c/restrict.html.   Broadly it's some kind of
anti-aliasing hint to the compiler. 


int accept(int socket, struct sockaddr *restrict address,
           socklen_t *restrict address_len);                       

int bind(int socket, const struct sockaddr *address, socklen_t address_len);

int close(int fildes);   

int connect(int socket, const struct sockaddr *address,
         socklen_t address_len);   

int fcntl(int fildes, int cmd, ...);   

int fgetpos(FILE *restrict stream, fpos_t *restrict pos);
int fsetpos(FILE *stream, const fpos_t *pos);
long ftell(FILE *stream);

- ignore fgetpos, fsetpos, ftell, as irrelevant?   

void freeaddrinfo(struct addrinfo *ai);

- ignore freeaddrinfo, as irrelevant for a purely-functional interface.  

int getaddrinfo(const char *restrict nodename,
                const char *restrict servname,
                const struct addrinfo *restrict hints,
                struct addrinfo **restrict res);    

int getpeername(int socket, struct sockaddr *restrict address,
                socklen_t *restrict address_len);

int getsockname(int socket, struct sockaddr *restrict address,
                socklen_t *restrict address_len);             

int getsockopt(int socket, int level, int option_name,
               void *restrict option_value, socklen_t *restrict option_len);

int setsockopt(int socket, int level, int option_name,
               const void *option_value, socklen_t option_len);   

int listen(int socket, int backlog);   

off_t lseek(int fildes, off_t offset, int whence);   

- ignore lseek, as not sensible for TCP

int poll(struct pollfd fds[], nfds_t nfds, int timeout);    

int pselect(int nfds, fd_set *restrict readfds,
            fd_set *restrict writefds, fd_set *restrict errorfds,
            const struct timespec *restrict timeout,
            const sigset_t *restrict sigmask);

int select(int nfds, fd_set *restrict readfds,
           fd_set *restrict writefds, fd_set *restrict errorfds,
           struct timeval *restrict timeout);   

- use only pselect

ssize_t pread(int fildes, void *buf, size_t nbyte, off_t offset); 
ssize_t read(int fildes, void *buf, size_t nbyte);   
ssize_t recv(int socket, void *buffer, size_t length, int flags);
ssize_t recvfrom(int socket, void *restrict buffer, size_t length,
                 int flags, struct sockaddr *restrict address,
                 socklen_t *restrict address_len);
ssize_t recvmsg(int socket, struct msghdr *message, int flags)   

ssize_t pwrite(int fildes, const void *buf, size_t nbyte, off_t offset); 
ssize_t write(int fildes, const void *buf, size_t nbyte);
ssize_t send(int socket, const void *buffer, size_t length, int flags);
ssize_t sendto(int socket, const void *message, size_t length,
               int flags, const struct sockaddr *dest_addr,
               socklen_t dest_len);
ssize_t sendmsg(int socket, const struct msghdr *message, int flags);   

- combine the receives and sends into one of each

int shutdown(int socket, int how);  

int sockatmark(int s);   

int socket(int domain, int type, int protocol);   

int socketpair(int domain, int type, int protocol, int socket_vector[2]);

- ignore socketpair, as irrelevant?   


%%%%%%%%%%%%%%%

and here is what we do with them:


val accept       : fd -> fd * ip lift * port lift 
val bind         : fd * ip lift * port lift                     -> unit 
val close        : fd                              -> unit 
val connect      : fd * ip * port lift                 -> unit 
(* val disconnect: fd                              -> unit                   *)


val fcntl : ????

(* not sure which of these we need. At least O_NONBLOCK ?*)



val getaddrinfo : ???

val getsockname  : fd                              -> ip lift * port lift
val getpeername  : fd                              -> ip lift * port lift


val getsockopt   : fd*sockopt                      -> bool                    
val setsockopt   : fd*sockopt*bool                 -> unit                    

(* need to think about which options, obviously *)



val listen : fd * int                              -> unit
val so_MAXCONN : int

val poll : (fd * event) list -> ???

val pselect       : fd list * fd list * int lift    -> (fd list * fd list) 
(* K: I think we should model the error set as well, since TCPv2p524
   says that this is used in detection of OOB data, i.e., urgent flag *)

val recvfrom     : fd*int*bool               -> string 

(* no need to return ip lift * port lift here, as its fixed for the connection??*)

val sendto       : fd* (ip * port) lift *string*bool -> unit 


(* really shouldn't use string here and above, as strings are mutable *)

type how = SHUT_RD | SHUT_WR | SHUT_RDWR
val shutdown : fd * how -> unit

(* K disagrees: should be

  val shutdown : fd * bool * bool -> unit

with noop for (F,F) case *)

val sockatmark : fd-> bool

val socket       : unit                            -> fd 


(* not sure if this is needed?
val geterr    : fd                              -> error lift             
*)

%%%%%%%%%%%%%






val port_of_int  : int                             -> port
val ip_of_string : string                          -> ip              
(* val getifaddrs: unit   -> (ifid * ip * ip list * netmask) list            *)

val create       : ('a -> 'b) -> 'a -> tid
val delay        : int -> unit

val print_endline_flush : string -> unit
val exit                : unit   -> void



-------------------

errors from

http://www.opengroup.org/onlinepubs/007904975/basedefs/errno.h.html


POSIX sockets calls that we're dealing with:

x is an error that may occur in our setting
z is an error that may occur in POSIX but not in our setting
b is an error that may occur in POSIX that we'd regard as a badfail


EAGAIN=EWOULDBLOACK is the only allowable alias.  I omit EWOULDBLOCK, mapping all such onto EAGAIN.

                              
                              
                   a b c c f g g g g s l p p p r r r r p w s s s s s s
                   c i l o c e e e e e i o s r e e e e w r e e e h o o
                   c n o n n t t t t t s l e e a c c c r i n n n u c c
                   e d s n t a p s s s t l l a d v v v i t d d d t k k
                   p   e e l d e o o o e   e d     f m t e   t m d a e
                   t     c   d e c c c n   c       r s e     o s o t t
                         t   r r k k k     t       o g         g w m  
                             i n n o o             m             n a  
                             n a a p p                             r  
                             f m m t t                             k  
                             o e e                                    
                              
[E2BIG]              
[EACCES]           
[EADDRINUSE]       
[EADDRNOTAVAIL]    
[EAFNOSUPPORT]     
[EAGAIN]           x
[EALREADY]         
[EBADF]            x
[EBADMSG]          
[EBUSY]            
[ECANCELED]        
[ECHILD]           
[ECONNABORTED]     x
[ECONNREFUSED]     
[ECONNRESET]       
[EDEADLK]          
[EDESTADDRREQ]     
[EDOM]             
[EDQUOT]           
[EEXIST]           
[EFAULT]           
[EFBIG]            
[EHOSTUNREACH]     
[EIDRM]            
[EILSEQ]           
[EINPROGRESS]      
[EINTR]            x
[EINVAL]           x
[EIO]              
[EISDIR]           
[ELOOP]            
[EMFILE]           x
[EMLINK]           
[EMSGSIZE]         
[EMULTIHOP]        
[ENAMETOOLONG]     
[ENETDOWN]         
[ENETRESET]        
[ENETUNREACH]      
[ENFILE]           x
[ENOBUFS]          b
[ENODATA]          
[ENODEV]           
[ENOENT]           
[ENOEXEC]          
[ENOLCK]           
[ENOLINK]          
[ENOMEM]           b
[ENOMSG]           
[ENOPROTOOPT]      
[ENOSPC]           
[ENOSR]            
[ENOSTR]           
[ENOSYS]           
[ENOTCONN]         
[ENOTDIR]          
[ENOTEMPTY]        
[ENOTSOCK]         x
[ENOTSUP]          
[ENOTTY]           
[ENXIO]            
[EOPNOTSUPP]       x
[EOVERFLOW]        
[EPERM]            
[EPIPE]            
[EPROTO]           b
[EPROTONOSUPPORT]  
[EPROTOTYPE]       
[ERANGE]           
[EROFS]            
[ESPIPE]           
[ESRCH]            
[ESTALE]           
[ETIME]            
[ETIMEDOUT]        
[ETXTBSY]          
[EXDEV]             



