(*:

  @section recv

M: Note I'm only describing the UDP semantics of recv...

  [[recv: (fd * int * msgflag list) -> (string * (ip * port) option)]].

  The argument of type [[fd]] is a file descriptor referring to the
  socket to receive data from. The [[int]] argument specifies the
  amount of data to read from that socket. The [[msgbflag list]] is a
  list of options to the [[recv]] call.

  The return value of the [[recv]] call is the data read from the
  socket of type [[string]] and the source address of that data [[(ip
  * port) option]].

  A call to [[recv()]] returns data from the datagram on the head of
  the socket's receive queue.

  A call to [[recv()]] may block if the socket's receive queue is
  empty, and will return when a datagram arrives. If the call does
  block then state [[Recv2(sid,n,opts)]] is entered.

  @specific UDP
  Because UDP is not a connect-oriented protocol, the socket may not
  be connected to a foreign peer and so the source address of the data
  will also be returned.

  @errors

  A call to [[recv()]] can fail with the errors below, in which case
  the corresponding  exception  is raised.

  @error [[EAGAIN]]

  Non-blocking behaviour is requested, either via the [[MSG_DONTWAIT]]
  flag being set in the [[recv]] option or via the [[O_NONBLOCK]] flag
  previously being set on the socket, and the call to [[recv]] would
  block, or there are no ephemeral ports left for autobinding to.

  @error [[EADDRNOTAVAIL]]

  There are no ephemeral ports left for autobinding to.

  @error [[ENOBUFS]]

  There are no ephemeral ports left for autobinding to.

  @error [[EOPNOTSUPP]]

  Out-of-band data is requested on BSD and Windows XP, or when the
  [[MSG_WAITALL]] flag is set on a [[recv]] call on Windows XP.

  @error [[ESHUTDOWN]]

  On Windows XP, a [[recv]] call is made on a socket that has been
  shutdown for reading.

  @error [[EMSGSIZE]]

  The amount of data requested in the [[recv]] call on Windows is less
  than the amount of data in the datagram on the head of the receive
  queue.

  @seealso [[badf_1]]  [[EBADF]]

  @seealso [[notsock_1]]  [[ENOTSOCK]]

  @commoncases
  [[recv_11]]; [[return_1]];
  [[recv_12]]; [[deliver_in_udp_1]]; [[recv_15]]; [[return_1]];

  @api

  BSD: ssize_t recvfrom(int s, void *buf, size_t len, int flags,
                        struct sockaddr *from, socklen_t *fromlen);

  Linux: int  recvfrom(int  s, void *buf, size_t len, int flags,
                       struct sockaddr *from, socklen_t *fromlen);

  WinXP: int recvfrom(SOCKET s, char* buf, int len, int flags,
                      struct sockaddr* from, int* fromlen);

  \begin{itemize}
  \item [[s]] is the file descriptor of the socket to receive from,
  corresponding to the [[fd]] argument of the model [[recv()]]

  \item [[buf]] is a value-result argument: when the call is made it
  is a pointer to a buffer to place the data received in, and upon
  return it holds the data received on the socket corresponding to the
  [[string]] return value of the model [[recv()]]

  \item [[len]] is the length of [[buf]] corresponding to the [[int]]
  argument of the model [[recv()]], the amount of data to be read from
  the socket

  \item [[flags]] is an OR-ing of the message flags that are set for
  the call corresponding to the [[msgbflag list]] argument of the
  model [[recv()]]

  \item [[from]] is a value-result argument: a pointer to a sockaddr
  structure when the call is made which is then filled in with the
  source address of the data received by the socket, corresponding to
  the [[(ip * port) option]] of the model [[recv()]]

  \item [[fromlen]] is the length of the [[from]] argument

  \item the returned [[int]] is the amount of data that was received
  by the socket

  \end{itemize}

 :*)


    (!h ts tid d socks sid sock udp n
      rcvq fd n0 opts0 data i3 ps3 opts rcvq'' data'
      fid ff sf is1 p1 is2 ps2 rcvq' datagram cantsndmore.

    recv_11 /* rp_all, fast succeed */
      h with <| ts := FUPDATE ts (tid, Timed(Run,d));
                socks := socks FUPDATE_LIST
                         [(sid,sock with <| pr := UDP_PROTO(udp with rcvq := rcvq) |>)] |>
    -- Lh_call (tid, recv(fd,n0,opts0)) -->
      h with <| ts := FUPDATE ts (tid, Timed(Ret (OK(IMPLODE data',SOME (i3,ps3))),sched_timer));
                socks := socks FUPDATE_LIST
                         [(sid,sock)] |>

    <==

       fd IN FDOM h.fds /\
       fid = h.fds ' fd /\
       FAPPLY h.files fid = File(FT_Socket(sid),ff) /\
       opts = LIST_TO_SET opts0 /\
       sock = Sock(SOME fid,sf,is1,SOME p1,is2,ps2,NONE,cantsndmore,F,UDP_PROTO(udp with rcvq := rcvq')) /\
       rcvq = (datagram with <| is := i3; ps := ps3; data := data |>)::rcvq'' /\
       rcvq' = (if MSG_PEEK IN opts then rcvq else rcvq'') /\
       n = clip_int_to_num n0 /\
       ((LENGTH data <= n /\ data = data' /\ windows_arch h.arch) \/
         (data' = TAKE n data /\ LENGTH data' = n /\ ~(windows_arch h.arch)))

   (*:

    @description

    Consider a UDP socket [[sid]]

    \begin{itemize}
    \item referenced by [[fd]]
    \item with at least one datagram on its receive queue
    \item bound to a local port
    \item not shutdown for reading
    \item and not in an error state.
    \end{itemize}

    A call [[recv(fd,n0,opts0]], where the socket [[sid]]'s receive
    queue has a datagram at its head consisting of data [[data] and
    source address [[i3,p3]], will succeed via an
    [[Lh_call(tid,recv(fd,n0,opts0))]] transition.

    The host will be left in state [[Ret (OK(IMPLODE
    data',SOME(i3,p3)))]] where data' is

    \begin{itemize}
    \item all of the data in the datagram, [[data]], if the amount of
    data requested [[n0]] is greater than or equal to the amount of
    data in the datagram
    \item or the first [[n0]] bytes of [[data]] if [[n0]] is less than
    the amount of data in the datagram, unless the platform is Windows
    XP (see below).
    \end{itemize}

    Additionally, the datagram is discarded from the receive queue
    even if all the data from it has not been read, unless the
    [[MSG_PEEK]] option is set in the [[opts0]] argument, in which
    case the entire datagram stays on the receive queue and further
    calls to [[recv]] will be able to access this datagram.



    @modelcomment

    The amount of data requested, [[n0]], is clipped to a number from
    an integer, using [[clip_int_to_num]]. POSIX specifies an unsigned
    type for [[n0]] and this is one possible implementation of this.

    The [[opts0]] argument to [[recv]] is of type [[msgbflag list]],
    but it is converted to a set, [[opts]], using [[LIST_TO_SET]] for
    the purposes of examining which flags are set.

    The data itself is represented as a [[byte list]] in [[datagram]]
    but is returned a [[string]], so the [[IMPLODE]] function is used
    to do the conversion.

    @variation WinXP
    When calling [[recv]] on Windows XP, the amount of data requested
    has to be greater than or equal to the amount of data in the
    datagram on the head of the receive queue. Otherwise see rule
    [[recv_20]]
    @variation BSD
    As above.
    @variation LINUX
    As above.
    @variation Posix
    As above.
    @variation RFC
    As above.

    @internal

   When a [[recv]] call is made on a UDP socket with data on the
   receive queue, data will be returned. If the amount of data
   requested, [[n]], is less than the amount of data in the datagram
   on the head of the receive queue, then on Linux and BSD, this
   amount of data is returned. On Windows, all of the data in the
   datagram is returned, but only when the amount of requested data is
   equal to or greater than the amount of data in the first datagram.

  If the [[MSG_PEEK]] flag is set then the datagram is left on the
  receive queue, otherwise it is removed, even if only some of the
  data it contains has been read.

   :*)



    )