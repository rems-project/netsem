#include <sys/types.h>
#include <sys/socket.h>
#include <dlfcn.h>
#include <stdio.h>
#include <fcntl.h>
#include <sys/stat.h>

int init = 0;

typedef int (*socket_ptr_t)(int, int, int);
static socket_ptr_t real_socket;

void initialise()
{
  void *handle = NULL;

  if ((handle = dlopen("/lib/libc.so.6", RTLD_LAZY)) == NULL)
  {
    printf("%s\n", dlerror());
    exit(1);
  }

  if ((real_socket = dlsym(handle, "socket")) == NULL)
  {
    printf("%s\n", dlerror());
    exit(1);
  }
}

int ns_socket(int domain, int type, int protocol)
{
  if(init == 0)
    initialise();

  fprintf(stderr, "ns_socket CALLED.\n");
  return real_socket(domain, type, protocol);
}
