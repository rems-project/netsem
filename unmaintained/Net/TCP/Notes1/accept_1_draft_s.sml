(*:

  @section accept

  accept: fd -> fd * (ip * port)

  [[accept(fd)]] returns the next connection available on the completed
  connections queue for the listening TCP socket referenced by file
  descriptor [[fd]].

  The [[fd]] of the return value refers to the newly-connected socket.
  The [[ip]] and [[port]] are the remote IP address and port of the
  newly-connected socket.

  [[accept(fd)]] blocks if the completed connections queue is empty
  and the socket does not have the [[O_NONBLOCK]] flag set.

P: not quite sure about the para below - doesn't make sense as is
unless we know all about pending errors and what [[ECONNABORTED]]
means.  Don't want to explain them in detail, though.

  All pending errors on the new connection are ignored, except for
  [[ECONNABORTED]] which causes [[accept()]] to fail with
  [[ECONNABORTED]].

  @specific UDP

  Calling [[accept()]] on a UDP socket will fail; UDP is not a
  connection-oriented protocol.

  @errors

  A call to [[accept()]] can fail with the errors below, in which case
  the corresponding exception is raised.

  @error [[ECONNABORTED]]

  The connection at the head of the completed connections queue has
  been aborted.

P (not done): should explain what "aborted" means

  @error [[EINVAL]]

  Ths socket is not accepting connections, \ie it is not in the
  [[LISTEN]] state.

  @error [[EAGAIN]]

  The socket has the [[O_NONBLOCK]] flag set and no connections are
  available on the completed connections queue.

  @error [[EINTR]]

  A blocked [[accept()]] call was interrupted by a signal before a
  completed connection arrived.

  @error [[ENFILE]]

  The maximum number of file descriptors in the system are already open.

  @error [[EMFILE]]

  The maximum number of file descriptors allowed per process are
  already open for this process.

  @error [[ENOBUFS]]

  No buffer space is available.

  @error [[ENOMEM]]

  There was insufficient memory to complete the operation.

  @error [[EOPNOTSUPP]]

  The socket type of the specified socket does not support accepting
  connections. This error is raised if [[accept()]] is called on a UDP socket.

  @seealso [[badf_1]]  EBADF

  @seealso [[notsock_1]]  ENOTSOCK

  ## Rule summary appears here ##

  @commoncases

  [[accept_1]]; [[return_1]]

  [[accept_2]]; [[deliver_in_1]]; [[accept_1]]; [[return_1]]

  @api

  Posix:   int accept(int socket, struct sockaddr *restrict address,
                      socklen_t *restrict address_len);

  Linux:   int accept(int s, struct sockaddr *addr, socklen_t *addrlen);

  FreeBSD: int accept(int s, struct sockaddr *addr, socklen_t *addrlen);

  WinXP:   SOCKET accept(SOCKET s, struct sockaddr* addr, int* addrlen);

  In the Posix interface:
  \begin{itemize}
  \item [[socket]] is the listening socket's file descriptor,
   corresponding to the [[fd]] argument of the model;

  \item the returned [[int]] is either non-negative, \ie a file
  descriptor referring to the newly-connected socket, or -1 if errno
  is set to indicate an error. The [[accept()]] model is defined to
  return the file descriptor of the newly-connected socket as error
  conditions are signalled through exceptions. On WinXP a return value
  of [[INVALID_SOCKET]] indicates an error, not -1.

  \item [[address]] is either null or a pointer to a sockaddr
  structure; if the latter, then the remote IP and port of the
  newly-connected socket are returned in it, corresponding to the
  [[ip*port]] returned by the [[accept()]] model;

  \item [[address_len]] is a pointer to a socklen_t structure which on
  input specifies the length of the sockaddr structure, and on output
  specifies the length of the stored address. This is not modelled
  because the model's abstract [[ip*port]] type has an implicit
  size. The WinXP documentation suggests that [[addrlen] can be null, in
  which case the sockaddr structure is not filled in even if a valid
  pointer is provided in [[addr]].  \end{itemize}

  The FreeBSD, Linux, and WinXP interfaces are similar except where noted.

  The following errors are not included in the model:
  \begin{itemize}
  \item [EFAULT]] signifies that the pointers passed as either the
  [[address]] or [[address_len]] arguments were inaccessible.  This is
  an artefact of the C interface to [[accept()]] that is excluded by
  the clean interface used here;

  \item [[EPERM]] is a Linux-specific error code described by the
  Linux man page as ``Firewall rules forbid connection''. This is
  outside the scope of what is modelled;

  \item [[EPROTO]] is a Linux-specific error code described by the man
  page as ``Protocol error``. Only TCP and UDP are modelled here; the
  only sockets that can exist in the model are bound to a known
  protocol.
  \end{itemize}

:*)

(!h lbl rc ts t files socks tid d fds fds'
  fd fid ff sid sf is1 i1' p1 i2 p2 es cb cb'
  q fd' fid' sid' sf' es' lis sndq rcvq
  cantsndmore cantrcvmore sndurp rcvurp iobc.

  accept_1 /* rc TCP (*: normal case :*) */
    h with <| ts := FUPDATE ts (tid,Timed(t,d));
              fds := fds;
              files := files;
              socks :=
                socks FUPDATE_LIST
                  [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,F,F,
                              TCP_Sock(LISTEN,cb,SOME (lis with <| q := sid' :: q |>),
                                       [],NONE,[],NONE,NO_OOBDATA)));
                   (sid',Sock(NONE,sf',SOME i1',SOME p1,SOME i2,SOME p2,es',
	            cantsndmore,cantrcvmore,TCP_Sock(ESTABLISHED,cb',NONE,
                                                     sndq,sndurp,rcvq,rcvurp,iobc)))] |>
  -- lbl -->
    h with <| ts := FUPDATE ts (tid,Timed(Ret (OK (fd',(i2,p2))),sched_timer));
              fds := fds';
              files := files FUPDATE_LIST [(fid',File(FT_Socket(sid'),ff_default))];
              socks :=
	        socks FUPDATE_LIST
                  [(sid ,Sock(SOME fid,sf,is1,SOME p1,NONE,NONE,es,F,F,
			      TCP_Sock(LISTEN,cb,SOME (lis with <| q := q |>),
				       [],NONE,[],NONE,NO_OOBDATA)));
                   (sid',Sock(SOME fid',sf',SOME i1',SOME p1,SOME i2,SOME p2,es',
		    cantsndmore,cantrcvmore,TCP_Sock(ESTABLISHED,cb',NONE,
                                                     sndq,sndurp,rcvq,rcvurp,iobc)))] |>

   <==

    $\/
    (t = Run /\ (*: Non-blocking case :*)
     lbl = Lh_call (tid,(accept fd)) /\
     rc = fast succeed /\
     fid = fds ' fd  /\
     fd IN FDOM fds /\
     FAPPLY files fid = File(FT_Socket(sid),ff)
    )
    (t = Accept2(sid) /\ (*: Return from blocking call :*)
     lbl = Lh_tau /\
     rc = slow urgent succeed
     ) /\
    sid <> sid' /\ (* redundant? *)
    es' <> SOME ECONNABORTED /\
    fid' NOTIN ((FDOM files) UNION {fid}) /\
    nextfd h.arch fds fd' /\
    fds' = fds |+ (fd', fid') /\
    (!i1. SOME i1 = is1 ==> i1 = i1')


   (*:

   @description

   Take the listening TCP socket [[sid]] referenced by file descriptor
   [[fd]], consider a connection [[sid'']] at the head of its completed
   connections queue [[sid'::q]]. A [[socket]] entry for [[sid']]
   already exists in the host's finite map of sockets [[h.socks]]. The
   socket is [[ESTABLISHED]] and is only missing a file description
   association that would make it accessible via the sockets
   interface.

   If the new socket [[sid']] has error [[ECONNABORTED]] pending in the
   error field [[es']], this is handled by rule [[accept_5]]. All
   other pending errors on [[sid']] are ignored.

   This rule covers two cases: (1) the completed connection queue is
   non-empty when [[accept()]] is called and the thread is presently
   in the [[Run]] state, and (2) a previous call to [[accept()]] on
   socket [[sid]] blocked leaving the thread in state
   [[Accept2(sid)]] and a new connection has become available.

   In either case a new file description record is created, indexed by
   [[fid']] for connection [[sid']], and this is added to the host's
   finite map of file descriptions [[h.files]].  The [socket]] entry
   [[sid']] is completed with its file association [[SOME fid']] and
   [[sid']] is removed from the head of the completed connections queue.

   If the listening socket [[sid]] is bound to a local IP address
   [[i1]] the accepted socket [[sid']] must also be bound to it.  ##If
   [[sid]] is not bound to a specific local IP address the local
   address of the accepted socket should be one of the IP addresses
   owned by this host ??##

   Finally, the new file descriptor [[fd']] is created in an
   architecture-specific way using the auxiliary [[nextfd]], and an
   entry mapping [[fd']] to [[fid']] is added to the host's finite map
   of file descriptors.  If the calling thread was previously blocked in state
   [[Accept2(sid)]] it proceeds via an [[Lh_tau]] transition, otherwise
   by a [[Lh_call((tid,(accept fd))]] transition.  The host is left in
   state [[Ret (OK (fd',(i2,p2)))]] to return the file descriptor and
   remote address of the accepted connection to the calling thread.

   @modelcomment

   None

   @variation FreeBSD

   @variation Linux

   @variation WinXP

   @variation Posix

   @variation RFC

   @internal

   If the queue of completed connections is non-empty and the user
   either calls [[accept()]] or has already made a blocking call to
   [[accept()]] (and is therefore now in state [[Accept2]]), then a
   new open file description is allocated for the socket, and a new
   file descriptor made to point to the open file description.
   Pending errors are ignored, except for [[ECONNABORTED]], of the
   provenance of which the present writer is uncertain (see
   [[accept_5]]).

   This rule is a combination of (the old) [[accept_1]] and
   [[accept_1a]].  DISCUSSION POINT: is it clear?

   Notice that we require that the source ip and port are the same for
   the listening socket and the accepted socket.  I can't see this in
   POSIX; needs to be checked with BSD and/or Linux.

   POSIX: "shall extract...".
   POSIX: "until a connection is present...".

   slow version SHOULD BE URGENT.

   Michael points out that we should check if we actually can allocate
   a fresh fd.

   SB: The linux man page reads: "Linux accept passes already-pending
   network errors on the new socket as an error code fom accept. This
   behaviour differs from the other BSD socket implementations..."

   :*)
   )
