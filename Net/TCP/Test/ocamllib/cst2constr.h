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

/* $Id: cst2constr.h,v 1.2 2002/09/25 11:23:22 smb50 Exp $ */

#ifdef __STDC__
value cst_to_constr(int n, int *tbl, int size, int deflt);
#else
value cst_to_constr();
#endif
