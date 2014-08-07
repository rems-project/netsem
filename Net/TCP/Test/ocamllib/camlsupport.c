#include <mlvalues.h>
#include <alloc.h>
#include <memory.h>
#include <misc.h>
#include <string.h>

CAMLprim value copy_string_len(char const *s, int len)
{
  CAMLparam0();
  CAMLlocal1(res);

  res = alloc_string(len);
  memmove(String_val(res), s, len);
  CAMLreturn(res);
}
