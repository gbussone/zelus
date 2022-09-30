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
  | Elocal _ -> None
  | Eglobal _ -> None
  | Econst _ -> None
  | Econstr0 _ -> None
  | Econstr1 _ -> None
  | Elast _ -> None
  | Eapp (_,
          { e_desc = Eglobal { lname = Modname { id = "sample" } } },
          [e]) ->
     Some e
  | Eapp _ -> None
  | Eop _ -> None
  | Etuple _ -> None
  | Erecord_access _ -> None
  | Erecord _ -> None
  | Erecord_with _ -> None
  | Etypeconstraint _ -> None
  | Epresent _ -> None
  | Ematch _ -> None
  | Elet _ -> None
  | Eseq _ -> None
  | Eperiod _ -> None
  | Eblock _ -> None
