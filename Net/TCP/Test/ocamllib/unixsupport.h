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

/* $Id: unixsupport.h,v 1.2 2002/09/24 16:25:59 smb50 Exp $ */

#ifdef HAS_UNISTD
#include <unistd.h>
#endif

#include <caml/mlvalues.h>

#define Nothing ((value) 0)

extern void ns_unix_error (int errcode, char * cmdname, value arg);
extern void ns_uerror (char * cmdname, value arg);

#define UNIX_BUFFER_SIZE 16384
