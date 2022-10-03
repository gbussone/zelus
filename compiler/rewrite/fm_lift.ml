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
  | Elocal _ -> false
  | Eglobal _ -> true
  | Econst _ -> true
  | Econstr0 _ -> true
  | Econstr1 (_, e_list) -> List.for_all expression e_list
  | Elast _ -> false
  | Eapp (_, op, [obs]) when not (Ztypes.is_probabilistic 0 op.e_typ) ->
     expression obs
  | Eapp _ -> false
  | Eop (_, e_list) -> List.for_all expression e_list
  | Etuple e_list -> List.for_all expression e_list
  | Erecord_access (e, _) -> expression e
  | Erecord l_e_list -> List.for_all (fun (_, e) -> expression e) l_e_list
  | Erecord_with (e, l_e_list) ->
     expression e && List.for_all (fun (_, e) -> expression e) l_e_list
  | Etypeconstraint (e, _) -> expression e
  | Epresent _ -> false
  | Ematch _ -> false
  | Elet _ -> false
  | Eseq (e1, e2) -> expression e1 && expression e2
  | Eperiod _ -> false
  | Eblock _ -> false
