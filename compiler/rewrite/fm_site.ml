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

let gen =
  let c = ref 0 in
  fun () ->
    incr c;
    Zaux.emake (Econst (Eint !c)) Initial.typ_int

let rec expression ({ e_desc = e_desc } as e) =
  match e_desc with
  | Elocal _ -> e
  | Eglobal _ -> e
  | Econst _ -> e
  | Econstr0 _ -> e
  | Econstr1 (c, e_list) ->
     { e with e_desc = Econstr1 (c, List.map expression e_list) }
  | Elast _ -> e
  | Eapp (app,
          ({ e_desc = Eglobal { lname = Modname { id = "sample" } } } as op),
          [dist]) ->
     { e with e_desc = Eapp (app, op, [Zaux.tuple [dist; gen ()]]) }
  | Eapp (app, op, e_list) ->
     { e with e_desc = Eapp (app, expression op, List.map expression e_list) }
  | Eop (op, e_list) ->
     { e with e_desc = Eop (op, List.map expression e_list) }
  | Etuple e_list -> { e with e_desc = Etuple (List.map expression e_list) }
  | Erecord_access (e_record, x) ->
     { e with e_desc = Erecord_access (expression e_record, x) }
  | Erecord l_e_list ->
     let l_e_list = List.map (fun (l, e) -> l, expression e) l_e_list in
     { e with e_desc = Erecord l_e_list }
  | Erecord_with (e_record, l_e_list) ->
     let l_e_list = List.map (fun (l, e) -> l, expression e) l_e_list in
     { e with e_desc = Erecord_with (expression e_record, l_e_list) }
  | Etypeconstraint (e', ty) ->
     { e with e_desc = Etypeconstraint (expression e', ty) }
  | Epresent (e_ph_list, e_opt) ->
     let e_ph_list = List.map (present_handler expression) e_ph_list in
     { e with e_desc = Epresent (e_ph_list, Option.map expression e_opt) }
  | Ematch (total, e_match, e_mh_list) ->
     let e_mh_list = List.map (match_handler expression) e_mh_list in
     { e with e_desc = Ematch (total, expression e_match, e_mh_list) }
  | Elet (l, e') -> { e with e_desc = Elet (local l, expression e') }
  | Eseq (e1, e2) -> { e with e_desc = Eseq (expression e1, expression e2) }
  | Eperiod p -> { e with e_desc = Eperiod (period p) }
  | Eblock (b, e') -> { e with e_desc = Eblock (block b, expression e') }

and period { p_phase = phase_opt; p_period = period } =
  { p_phase = Option.map expression phase_opt; p_period = expression period }

and equation ({ eq_desc = eq_desc } as eq) =
  match eq_desc with
  | EQeq (p, e) -> { eq with eq_desc = EQeq (p, expression e) }
  | EQder (x, e, e_opt, e_ph_list) ->
     let e_opt = Option.map expression e_opt in
     let e_ph_list = List.map (present_handler expression) e_ph_list in
     { eq with eq_desc = EQder (x, expression e, e_opt, e_ph_list) }
  | EQinit (x, e) -> { eq with eq_desc = EQinit (x, expression e) }
  | EQnext (x, e, e_opt) ->
     let e_opt = Option.map expression e_opt in
     { eq with eq_desc = EQnext (x, expression e, e_opt) }
  | EQpluseq (x, e) -> { eq with eq_desc = EQpluseq (x, expression e) }
  | EQautomaton (weak, sh_list, se_opt) ->
     let sh_list = List.map state_handler sh_list in
     let se_opt = Option.map state_exp se_opt in
     { eq with eq_desc = EQautomaton (weak, sh_list, se_opt) }
  | EQpresent (b_ph_list, b_opt) ->
     let b_ph_list = List.map (present_handler block) b_ph_list in
     let b_opt = Option.map block b_opt in
     { eq with eq_desc = EQpresent (b_ph_list, b_opt) }
  | EQmatch (total, e, b_mh_list) ->
     let b_mh_list = List.map (match_handler block) b_mh_list in
     { eq with eq_desc = EQmatch (total, expression e, b_mh_list) }
  | EQreset (eq_list, e) ->
     { eq with eq_desc = EQreset (List.map equation eq_list, expression e) }
  | EQemit (x, e_opt) ->
     { eq with eq_desc = EQemit (x, Option.map expression e_opt) }
  | EQblock b -> { eq with eq_desc = EQblock (block b) }
  | EQand eq_list -> { eq with eq_desc = EQand (List.map equation eq_list) }
  | EQbefore eq_list ->
     { eq with eq_desc = EQbefore (List.map equation eq_list) }
  | EQforall fh -> { eq with eq_desc = EQforall (forall_handler fh) }

and block ({ b_locals = l_list; b_body = eq_list } as b) =
  { b with b_locals = List.map local l_list;
           b_body = List.map equation eq_list }

and local ({ l_eq = eq_list } as l) =
  { l with l_eq = List.map equation eq_list }

and state_handler ({ s_body = b; s_trans = esc_list } as sh) =
  { sh with s_body = block b; s_trans = List.map escape esc_list }

and state_exp se =
  match se.desc with
  | Estate0 _ -> se
  | Estate1 (x, e_list) ->
     { se with desc = Estate1 (x, List.map expression e_list) }

and escape ({ e_cond = s; e_block = b_opt; e_next_state = se } as esc) =
  { esc with e_cond = scondpat s;
             e_block = Option.map block b_opt;
             e_next_state = state_exp se }

and scondpat s =
  match s.desc with
  | Econdand (s1, s2) -> { s with desc = Econdand (scondpat s1, scondpat s2) }
  | Econdor (s1, s2) -> { s with desc = Econdor (scondpat s1, scondpat s2) }
  | Econdexp e -> { s with desc = Econdexp (expression e) }
  | Econdpat (e, pat) -> { s with desc = Econdpat (expression e, pat) }
  | Econdon (s', e) -> { s with desc = Econdon (scondpat s', expression e) }

and match_handler : type a. (a -> a) -> a match_handler -> a match_handler =
  fun f ({ m_body = body } as mh) -> { mh with m_body = f body }

and present_handler :
  type a. (a -> a) -> a present_handler -> a present_handler =
  fun f ({ p_cond = s; p_body = body } as ph) ->
  { ph with p_cond = scondpat s; p_body = f body }

and forall_handler
    ({ for_index = indexes_list; for_init = init_list; for_body = b } as fh) =
  { fh with for_index = List.map indexes indexes_list;
            for_init = List.map init init_list;
            for_body = block b }

and indexes i =
  match i.desc with
  | Einput (x, e) -> { i with desc = Einput (x, expression e) }
  | Eoutput _ -> i
  | Eindex (x, e1, e2) ->
     { i with desc = Eindex (x, expression e1, expression e2) }

and init i =
  match i.desc with
  | Einit_last (x, e) -> { i with desc = Einit_last (x, expression e) }

let implementation impl =
  match impl.desc with
  | Eopen _ -> impl
  | Etypedecl _ -> impl
  | Econstdecl (n, static, e) ->
     { impl with desc = Econstdecl (n, static, expression e) }
  | Efundecl (n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl (n, { body with f_body = expression e }) }

let implementation_list impl_list = Zmisc.iter implementation impl_list
