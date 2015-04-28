#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/misc.h>

#include <string.h>

CAMLprim value copy_string_len(char const *s, int len)
{
  CAMLparam0();
  CAMLlocal1(res);

  res = alloc_string(len);
  memmove(String_val(res), s, len);
  CAMLreturn(res);
}
