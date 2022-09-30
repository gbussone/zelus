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

let empty = Zident.Env.empty
let add = Zident.Env.add
let map_eq = Zident.Env.map (fun e -> Some e)
let filter = Zident.Env.filter_map (fun _ o -> o)
let union env1 env2 = Zident.Env.union (fun _ _ _ -> assert false) env1 env2
let union_eq env1 env2 =
  Zident.Env.union
    (fun _ o1 o2 ->
       match o1, o2 with
       | None, _ | _, None -> None
       | Some _, Some _ -> assert false)
    env1 env2

let rec pattern p =
  match p.p_desc with
  | Ewildpat -> empty
  | Econstpat _ -> empty
  | Econstr0pat _ -> empty
  | Econstr1pat (_, p_list) ->
     List.fold_left union_eq empty (List.map pattern p_list)
  | Etuplepat p_list -> List.fold_left union_eq empty (List.map pattern p_list)
  | Evarpat x -> add x None empty
  | Ealiaspat (p, x) -> add x None (pattern p)
  | Eorpat (p1, p2) -> union_eq (pattern p1) (pattern p2)
  | Erecordpat l_p_list ->
     List.fold_left union_eq empty
       (List.map (fun (_, p) -> pattern p) l_p_list)
  | Etypeconstraintpat (p, _) -> pattern p

let rec expression e =
  match e.e_desc with
  | Elocal _ -> empty
  | Eglobal _ -> empty
  | Econst _ -> empty
  | Econstr0 _ -> empty
  | Econstr1 (_, e_list) ->
     List.fold_left union empty (List.map expression e_list)
  | Elast _ -> empty
  | Eapp (_, op, e_list) ->
     List.fold_left union (expression op) (List.map expression e_list)
  | Eop (_, e_list) ->
     List.fold_left union empty (List.map expression e_list)
  | Etuple e_list -> List.fold_left union empty (List.map expression e_list)
  | Erecord_access (e_record, _) -> expression e_record
  | Erecord l_e_list ->
     List.fold_left union empty
       (List.map (fun (_, e) -> expression e) l_e_list)
  | Erecord_with (e_record, l_e_list) ->
     List.fold_left union (expression e_record)
       (List.map (fun (_, e) -> expression e) l_e_list)
  | Etypeconstraint (e, _) -> expression e
  | Epresent _ -> empty (* TODO *)
  | Ematch _ -> empty (* TODO *)
  | Elet (l, e) -> union (local l) (expression e)
  | Eseq (e1, e2) -> union (expression e1) (expression e2)
  | Eperiod _ -> empty (* TODO *)
  | Eblock (b, e) -> union (block b) (expression e)

and equation eq =
  match eq.eq_desc with
  | EQeq (p, e) -> union_eq (pattern p) (map_eq (expression e))
  | EQder _ -> assert false
  | EQinit (x, e) -> Zident.Env.add x (Some e) (map_eq (expression e))
  | EQnext _ -> assert false
  | EQpluseq (x, e) -> Zident.Env.add x None (map_eq (expression e))
  | EQautomaton _ -> assert false
  | EQpresent _ -> assert false
  | EQmatch _ -> empty (* TODO *)
  | EQreset _ -> assert false
  | EQemit _ -> assert false
  | EQblock b -> map_eq (block b)
  | EQand eq_list -> List.fold_left union_eq empty (List.map equation eq_list)
  | EQbefore eq_list ->
      List.fold_left union_eq empty (List.map equation eq_list)
  | EQforall _ -> assert false

and block b =
  List.fold_left union
    (filter (List.fold_left union_eq empty (List.map equation b.b_body)))
    (List.map local b.b_locals)

and local l = filter (List.fold_left union_eq empty (List.map equation l.l_eq))
