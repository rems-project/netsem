#include <winsock2.h>
#include <windows.h>
#include <stdio.h>

/* WARNING: win32 environments are buffers that contain null-terminated  */
/* strings of the form "var=value" concatenated and followed by an extra */
/* null at the end, i.e. at the end of the buffer there are *two* null   */
/* values! */

/* Error reporting function */

void error_abort(char *msg)
{
  fprintf(stderr, "custom_rsh: %s\n", msg);
  abort();
}

void warning(char *msg)
{
#ifdef DEBUG
  fprintf(stderr, "custom_rsh: %s\n", msg);
#endif
}

void wsa_error_abort(char *msg)
{
  int err;

  err = WSAGetLastError();
  fprintf(stderr, "custom_rsh: winsock error -- %s(%d)\n", strerror(err), err);
  error_abort(msg);
}


/* Initialise winsock */
void initWinsock()
{
  WORD wVersionRequested;
  WSADATA wsaData;
  int err;

  //Initialise the winsock library (version 2.2 compat)
  wVersionRequested = MAKEWORD(2, 2);
  err = WSAStartup(wVersionRequested, &wsaData);
  if (err != 0)
   error_abort("Could not init winsock\n");

  if (LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
    WSACleanup();
    error_abort("Could not init winsock. Version 2 not available\n");
  }
}


/* Worker thread: read the execution string from the connected socket, */
/* parse the commands and create the required process with the correct */
/* environment. Wait until the socket is disconnected then kill the    */
/* previously created process, release all memory and close the socket */
DWORD WINAPI thread_body(LPVOID lpsock) {
  SOCKET sdconn;
  char recv_buf[2048], *progpath, *oldenv, *newenv;
  int recv_len, i, j, endofenv=0;
  int oldlen1, oldlen2, newlen=0;
  PROCESS_INFORMATION pinfo;
  STARTUPINFO sinfo;

  ZeroMemory(&sinfo, sizeof(sinfo));
  sinfo.cb = sizeof(sinfo);
  ZeroMemory(&pinfo, sizeof(pinfo));


  //Copy in the sock descriptor and free the temporary memory allocation
  memcpy(&sdconn, lpsock, sizeof(SOCKET));
  free(lpsock);

  /* Read command from connected socket */
  ZeroMemory(recv_buf, 2048);
  recv_len = recv(sdconn, recv_buf, 2048, 0);
  if(recv_len == 0)  {
    warning("recv returned end-of-file");
    goto exit;
  } else if(recv_len == SOCKET_ERROR)
    wsa_error_abort("recv raised an error");

  /* Decide which netsem tool to run */
  switch(recv_buf[0]) {
    case 'S':
#ifdef DEBUG
      printf("SLURP\n");
#endif
      if((progpath = getenv("EXEC_SLURP")) == NULL)
        error_abort("EXEC_SLURP not found in the environment");
      break;
    case 'L':
#ifdef DEBUG
      printf("LIBD\n");
#endif
      if((progpath = getenv("EXEC_LIBD")) == NULL)
        error_abort("EXEC_LIBD not found in the environment");
      break;
    case 'I':
#ifdef DEBUG
      printf("INJECTOR\n");
#endif
      if((progpath = getenv("EXEC_INJECTOR")) == NULL)
        error_abort("EXEC_INJECTOR not found in the environment");
      break;
    case 'T':
      error_abort("TCP_DEBUG not supported on windows");
      break;
    case 'C':
      if((progpath = getenv("EXEC_TSCCAL")) == NULL)
	error_abort("EXEC_TSCCAL not found in the environment");
      break;
    default:
      error_abort("received an unknown program command");
      break;
  }

#ifdef DEBUG
  printf("progpath: %s\n", progpath);
  printf("cmdline: %s\n", &recv_buf[1]);
#endif

  /* Replace each * and $ with a null */
  /* Record the position of the first * -- this is */
  /* the index of the end of the environment vars  */
  for(i=0; i<2048; i++)
    if(recv_buf[i] == '*') {
      recv_buf[i] = '\0';
      if(endofenv == 0) endofenv = i;
    } else if(recv_buf[i] == '$') {
      recv_buf[i] = '\0';
    }
  oldlen1 = endofenv;  //length of environment vars from socket

  /* Get the current process's environment */
  oldenv = GetEnvironmentStrings();
  for(i=0; ; i++)
    if(oldenv[i] == '\0' && oldenv[i+1] == '\0')
      break;
  oldlen2 = i+1;      //length of the current process's environment */

  /* Create buffer for the new environment */
  newlen = oldlen1 + oldlen2 + 1;
  if((newenv = malloc(newlen)) == NULL)
    error_abort("malloc failed");

  /* Copy the current process's environment and the environment */
  /* from the socket into the new environment buffer */
  for(i=0; i<oldlen2; i++)
    newenv[i] = oldenv[i];
  for(j=1; j<oldlen1; j++,i++)
    newenv[i] = recv_buf[j];

  /* Put the mandatory extra null on the end of the new environment */
  newenv[i] = '\0';

  /* Create the process */
  if(!CreateProcess(progpath, &recv_buf[endofenv+1], NULL, NULL, TRUE, 0, newenv, NULL, &sinfo, &pinfo))
    error_abort("create process failed");


  /* Wait until the connection dies */
  while(1) {
    recv_len = recv(sdconn, recv_buf, 2048, 0);
    if(recv_len == 0 || recv_len == SOCKET_ERROR) {
      /* Kill the process and exit */
#ifdef WIN32
      printf("Killing\n");
#endif
      free(newenv);
      FreeEnvironmentStrings(oldenv);
      TerminateProcess(pinfo.hProcess, 0);
      break;
    }
  }

exit:
  //Close the socket now we are done
  if(closesocket(sdconn) == SOCKET_ERROR)
    wsa_error_abort("close of connected socket failed");

  return 0;
}


int main(int argc, char *argv[])
{
  SOCKET sd, newconn, *tempsd;
  HANDLE threadHnd;
  DWORD threadId;
  struct sockaddr_in bind_addr, newconn_addr;
  int newconn_size;

  if(argc != 3)
    error_abort("Incorrect args: custom_rsh ip_addr port");

  initWinsock();

  if((sd = socket(AF_INET, SOCK_STREAM, 6)) == INVALID_SOCKET)
    wsa_error_abort("Call to socket() failed");

  ZeroMemory(&bind_addr, sizeof(bind_addr));
  bind_addr.sin_family = AF_INET;
  bind_addr.sin_addr.s_addr = inet_addr(argv[1]);
  bind_addr.sin_port = htons(atoi(argv[2]));
  if(bind(sd, (struct sockaddr*)&bind_addr, sizeof(bind_addr)) == SOCKET_ERROR)
    wsa_error_abort("bind() failed");

  if(listen(sd, 10) == SOCKET_ERROR)
    wsa_error_abort("listen() failed");

  /* Accept new connections and pass them to a worker thread */
  while(1) {
    ZeroMemory(&newconn_addr, sizeof(newconn_addr));

    newconn_size = sizeof(newconn_addr);
    if((newconn = accept(sd, (struct sockaddr*)&newconn_addr, &newconn_size)) == INVALID_SOCKET) {
      wsa_error_abort("accept() failed but will continue anyway");
      continue;
    }

    /* Need to pass a copy of the sd to eliminate the obvious race condition */
    /* Thread is responsible of calling free() */
    if((tempsd = malloc(sizeof(SOCKET))) == NULL) {
      warning("malloc failed but will continue");
      continue;
    }
    memcpy(tempsd, &newconn, sizeof(SOCKET));

    if((threadHnd = CreateThread(NULL, 0, thread_body, tempsd, 0, &threadId)) == NULL) {
      warning("CreateThread() failed but will continue anyway");
      continue;
    }
  }

  WSACleanup();
  return 0;
}
