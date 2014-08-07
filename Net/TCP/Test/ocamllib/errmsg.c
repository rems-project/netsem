/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../../LICENSE.  */
/*                                                                     */
/***********************************************************************/

/* $Id: errmsg.c,v 1.6 2004/06/24 11:09:33 smb50 Exp $ */

#include <errno.h>
#include <mlvalues.h>
#include <alloc.h>
#include <memory.h>
#include <misc.h>

extern int ns_error_table[];

#ifdef HAS_STRERROR

extern char * strerror(int);

CAMLprim value unix_error_message(value err)
{
  CAMLparam1(err);
  int errnum;
  errnum = Is_block(err) ? Int_val(Field(err, 0)) : ns_error_table[Int_val(err)];
  CAMLreturn(copy_string(strerror(errnum)));
}

#else

extern int sys_nerr;
extern char *sys_errlist[];

CAMLprim value unix_error_message(value err)
{
  CAMLparam1(err);
  int errnum;
  errnum = Is_block(err) ? Int_val(Field(err, 0)) : ns_error_table[Int_val(err)];
  if (errnum < 0 || errnum >= sys_nerr) {
    CAMLreturn(copy_string("Unknown error"));
  } else {
    CAMLreturn(copy_string(sys_errlist[errnum]));
  }
}

#endif
