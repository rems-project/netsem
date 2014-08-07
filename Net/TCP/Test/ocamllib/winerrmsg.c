/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 2001 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../../LICENSE.  */
/*                                                                     */
/***********************************************************************/

/* $Id: winerrmsg.c,v 1.7 2004/06/24 11:09:34 smb50 Exp $ */

#include <errno.h>
#include <string.h>
#include <mlvalues.h>
#include <alloc.h>
#include <memory.h>
#include <misc.h>
#include "unixsupport.h"
#include <wtypes.h>
#include <winbase.h>

extern char *geterrmsg(char *dest, int errno);
extern int ns_error_table[];

CAMLprim value unix_error_message(value err)
{
  CAMLparam1(err);
  int errnum, len;
  char buffer[512];

  errnum = Is_block(err) ? Int_val(Field(err, 0)) : ns_error_table[Int_val(err)];
  if (errnum > 0)
    return copy_string(strerror(errnum));

  //call nssock function
  geterrmsg(buffer, -errnum);
  len = strlen(buffer);
  if(len > 0) {
	buffer[len] = ':';
	buffer[len+1] = ' ';
	buffer[len+2] = '\0';
  }

  if (FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
                    NULL, -errnum, 0, buffer+strlen(buffer),
		    sizeof(buffer) - strlen(buffer), NULL))
    CAMLreturn(copy_string(buffer));

  strcat(buffer, "unknown error");
  CAMLreturn(copy_string(buffer));
}
