(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* translation of inference calls. *)

(* every call to an inference function:

   [Infer.infer fm_params (model, obs)]

is translated into:

   [Infer.infer fm_params (Infer.mk_model model, obs)]
 *)

open Zelus

let rec expression e =
  match e.e_desc with
  | Elocal _
  | Eglobal _
  | Econst _
  | Econstr0 _
  | Econstr1 _
  | Elast _
  | Eapp _
  | Eop _
  | Etuple _
  | Erecord_access _
  | Erecord _
  | Erecord_with _
  | Etypeconstraint _
  | Epresent _
  | Ematch _
  | Elet _
  | Eseq _
  | Eperiod _
  | Eblock _ -> true (* TODO *)
