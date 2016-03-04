 (*:
  @section send

  send: (fd * (ip * port) option * string * msgbflaglist) -> string.

  The argument of type [[fd]] is a file descriptor referring to the
  socket from which to send data. The [[(ip * port) option]] is the
  destination address of the data. The [[string]] is the data to be
  sent. The [[msgbflag list]] is the list of message flags for the
  [[send]] call.

  The return value of the [[send]] call is a [[string]] of the data
  which was not sent.

M: note I'm only doing the UDP send description

P: y.  In fact for send and receive TCP and UDP should have sepearate
preambles.


  A call to [[send()]] sends a datagram to another socket.

  A call to [[send()]] may block, entering state [[Send2(...)]] if
  there is no room on the socket's send buffer.

  @specific UDP
  As UDP is not a connection-oriented protocol, if the
  socket is not currently connected to a peer, then a destination
  address must be specified when the call to [[send]] is made. The
  socket is then temporarily connected to this address, then the
  datagram is sent, and it is then disconnected.

  @errors

  A call to [[send()]] can fail with the errors below, in which case
  the corresponding exception is raised.

  @error [[EAGAIN]]
  Non-blocking behaviour is requested, either via
  the [[MSG_DONTWAIT]] flag being set in the [[send]] option or by the
  [[O_NONBLOCK]] flag previously being set on the socket, and the
  [[send]] call would block, or there are no ephemeral ports left for
  autobinding to.

  @error [[ENOTCONN]]
  The socket is unconnected and a
  destination address is not specified, either when the call is first
  made, or if it first blocks and is disconnected whilst blocked.

  @error [[EDESTADDRREQ]]
  The socket is unconnected and a destination address is not
  specified.

  @error [[EMSGSIZE]]
  The data attempting to be sent more than the maximum allowed length
  of data in a UDP datagram.

  @error [[EADDRNOTAVAIL]]
  There are no ephemeral ports left for autobinding to.

  @error [[ENOBUFS]]
  There are no ephemeral ports left for autobinding to.

  @error [[EINTR]]
  The call blocked and was then interrupted by a signal.

  @error [[EADDRNINUSE]]
  The socket is unconnected and the destination address specified
  would temporarily give the socket the binding quad [[i1,p1,i2,p2]]
  which is already being used by another socket.

  @error [[EOPNOTSUPP]]
  The [[MSG_OOB]] flag is set on Linux or Windows.

  @seealso [[badf_1]] [[EBADF]]
  @seealso [[notsock_1]] [[ENOTSOCK]]


  @common-cases
  [[send_9]]; [[return_1]];

  @api
  BSD: ssize_t sendto(int s, const void *msg, size_t len, int flags,
                      const struct sockaddr *to, socklen_t tolen);

  Linux: int sendto(int s, const void *msg, size_t len, int flags,
                    const struct sockaddr *to, socklen_t tolen);

  WinXP: int sendto(SOCKET s, const char* buf, int len, int flags,
                    const struct sockaddr* to, int tolen);

  Posix:

  \begin{itemize}
  \item [[s]] is the file descriptor of the socket to send from,
  corresponding to the [[fd]] argument of the model [[send()]]

  \item [[msg]] is a pointer to the data to be sent, corresponding to
  the [[string]] argument of the model [[send()]]

  \item [[len]] is the length of [[msg]]

  \item [[flags]] is a OR-ing of the message flags for the [[send]]
  call, corresponding to the [[msgbflag list]] in the model [[send()]]

  \item [[from]] is either null or a pointer to a sockaddr structure
  containing the destination address for the data; if it is null it
  corresponds to the [[(ip * port) option]] argument of the model
  being [[NONE]] and if it contains an address then it corresponds to
  the the argument being [[SOME]] address

  \item [[fromlen]] is the length of the [[from]] structure.

  \item the returned [[int]], or [[ssize_t]] in BSD, is the amount of
  data from [[msg]] that was sent which is different to the model [[send]]'s return
  value of type [[string]] which is the data that was not sent.

  \end{itemize}

  :*)


   (!h ts tid d socks sid sock fd udp h0
     addr str opts0 p1' oq' fid ff.

   send_9 /* rp_all, fast succeed (*: autobinding :*) */
      h0
    -- Lh_call (tid,send(fd,addr,IMPLODE str,opts0)) -->
      h with <| ts := FUPDATE ts (tid, Timed(Ret (OK ()),sched_timer));
                socks := socks FUPDATE_LIST
                         [(sid,sock with <| es := NONE; ps1 := SOME p1' |>)];
                oq := oq' |>


    <==

      h0 = h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                     socks := socks FUPDATE_LIST
                              [(sid,sock with <| es := NONE; pr := UDP_PROTO(udp) |>)] |> /\
      fd IN FDOM h0.fds /\
      fid = h0.fds ' fd /\
      FAPPLY h0.files fid = File(FT_Socket(sid),ff) /\
      p1' IN autobind(sock.ps1, h0.socks) /\
      dosend(h.ifds,h.rttab,(addr,str),(sock.is1,SOME p1',sock.is2,sock.ps2),h0.oq,oq',T) /\
      STRLEN (IMPLODE str) <= UDPpayloadMax /\
      ((addr <> NONE) \/ (sock.is2 <> NONE)) /\
      sock.cantsndmore = F

    (*:

     @description

     For a UDP socket [[sid]] referenced by [[fd]], not shutdown for
     writing, and not in an error state, a call
     [[send(fd,addr,IMPLODE str,opts0)]] where

     \begin{itemize}
     \item the length of [[str]] is less than the maximum payload for a
     UDP datagram, [[UDPpayloadMax]],
     \item either the socket is already connected to a peer or the
     [[addr]] argument is [[SOME]] address,
     \item either the socket is already bound to a local port or it
     can be autobound,
     \item and a UDP datagram constructed from the socket's binding
     quad [[(sock.is1,SOME p1',sock.is2,sock.ps2)]], the destination
     address argument [[addr]], and the data [[str]], can be placed on
     the outqueue of the host, [[oq]] using the auxilliary function
     [[dosend]],
     \end{itemize}

     will succeed leaving the host in state [[Ret (OK())]] with new
     outqueue [[oq']] via a transition
     [[Lh_call(tid,send(fd,addr,IMPLODE str,opts0))]].


     @modelcomment

     The data to be sent is of type [[string]] in the [[send]] call
     but is a [[byte list]] when the datagram is constructed. Here the
     data, [[str]] is of type [[byte list]] and in the transition
     [[IMPLODE str]] is used to convert it into a string.

     @variation BSD
     @variation WinXP
     @variation Linux
     @variation Posix
     @variation RFC

     @internal

    )
