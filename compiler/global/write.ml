(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* compute write variables for every equation and block *)

open Ident
open Zelus
open Deftypes
   
let rec fv_pat bounded acc { pat_desc } =
  match pat_desc with
  | Ewildpat | Econstr0pat _ | Econstpat _ -> acc
  | Evarpat(x) -> 
     if (S.mem x acc) || (S.mem x bounded) then acc else S.add x acc
  | Econstr1pat(_, pat_list) | Etuplepat(pat_list) ->
     List.fold_left (fv_pat bounded) acc pat_list
  | Erecordpat(label_pat_list) ->
     List.fold_left
       (fun acc (_, p) -> fv_pat bounded acc p) acc label_pat_list
  | Ealiaspat(p, name) ->
     let acc = 
       if (S.mem name acc) || (S.mem name bounded)
       then acc else S.add name acc in
     fv_pat bounded acc p
  | Eorpat(p1, _) -> fv_pat bounded acc p1
  | Etypeconstraintpat(p, _) -> fv_pat bounded acc p

                          
(* computes [dv] and [di] *)
let rec equation ({ eq_desc } as eq)=
  let eq_desc, def =
    match eq_desc with
    | EQeq(pat, e) ->
       EQeq(pat, expression e),
       { Deftypes.empty with dv = fv_pat S.empty S.empty pat }
    | EQder(x, e) ->
       EQder(x, expression e),
       { Deftypes.empty with der = S.singleton x }
    | EQinit(x, e) ->
       EQinit(x, expression e),
       { Deftypes.empty with di = S.singleton x }
    | EQemit(x, e_opt) ->
       EQemit(x, Util.optional_map expression e_opt),
       { Deftypes.empty with dv = S.singleton x }
    | EQreset(eq, e) ->
       let eq, def = equation eq in
       EQreset(eq, expression e), def
    | EQand(and_eq_list) ->
       let and_eq_list, def =
         Util.mapfold
           (fun acc eq ->
             let eq, def = equation eq in eq, Deftypes.union def acc)
           Deftypes.empty and_eq_list in
       EQand(and_eq_list), def
    | EQlocal(b_eq) ->
       let b_eq, def_eq, _ = block b_eq in
       EQlocal(b_eq), def_eq
    | EQif(e, eq1, eq2) ->
       let e = expression e in
       let eq1, def1 = equation eq1 in
       let eq2, def2 = equation eq2 in
       let def = Deftypes.union def1 def2 in
       EQif(e, eq1, eq2), def
    | EQmatch({ e; handlers } as m) ->
       let match_handler acc ({ m_body } as m) =
         let m_body, def_body = equation m_body in
         { m with m_body = m_body }, Deftypes.union acc def_body in
       let e = expression e in
       let handlers, def =
         Util.mapfold match_handler Deftypes.empty handlers in
       EQmatch({ m with e; handlers }), def
    | EQautomaton({ handlers } as a_h) ->
       let handlers, def =
         Util.mapfold automaton_handler empty handlers in
       EQautomaton({ a_h with handlers }), def
    | EQpresent({ handlers; default_opt }) ->
       let present_handler acc ({ p_body } as p) =
         let p_body, def_body = equation p_body in
         { p with p_body = p_body }, Deftypes.union acc def_body in
       let handlers, def =
         Util.mapfold present_handler Deftypes.empty handlers in
       let default_opt, def_opt =
         match default_opt with
         | NoDefault -> NoDefault, Deftypes.empty
         | Init(eq) -> let eq, def = equation eq in Init(eq), def
         | Else(eq) -> let eq, def = equation eq in Else(eq), def in
       EQpresent({ handlers; default_opt }), Deftypes.union def def_opt
    | EQempty -> EQempty, Deftypes.empty
    | EQassert(e) -> EQassert(expression e), Deftypes.empty in
  (* set the names defined in the equation *)
  { eq with eq_desc = eq_desc; eq_write = def }, def

  
(** [returns a new block whose body is an equation [eq];
 *- the defined variables in [eq] that are not local;
 *- the defined local variables *)
and block ({ b_vars; b_body } as b) =
  let b_vars, dv_b = Util.mapfold vardec S.empty b_vars in
  let b_eq, def_eq = equation b_body in
  let def = Deftypes.diff def_eq dv_b in
  { b with b_vars; b_body; b_write = def }, def, dv_b
  
and vardec acc ({ var_name; var_default; var_init } as v) =
  { v with var_default = Util.optional_map expression var_default;
           var_init = Util.optional_map expression var_init },
  S.add var_name acc

and state ({ desc } as se) =
  match desc with
  | Estate0 _ -> se
  | Estate1(f, e_list) ->
     { se with desc = Estate1(f, List.map expression e_list) }
  | Estateif(e, se1, se2) ->
     { se with desc = Estateif(expression e, state se1, state se2) }

and automaton_handler acc ({ s_body; s_trans } as h) =
  let s_body, def_eq, dv_b = block s_body in
  let s_trans, def_escape = Util.mapfold escape Deftypes.empty s_trans in
  { h with s_body; s_trans },
  Deftypes.union (Deftypes.union def_eq (Deftypes.diff def_escape dv_b)) acc

and escape acc ({ e_cond; e_body; e_next_state } as esc) =
  let e_cond = scondpat e_cond in
  let e_body, def_eq, _ = block e_body in
  let e_next_state = state e_next_state in
  { esc with e_cond = e_cond; e_body = e_body; e_next_state = e_next_state },
  Deftypes.union def_eq acc
  
and scondpat ({ desc } as scpat) =
  let desc = match desc with
    | Econdand(scpat1, scpat2) ->
       Econdand(scondpat scpat1, scondpat scpat2)
    | Econdor(scpat1, scpat2) ->
       Econdor(scondpat scpat1, scondpat scpat2)
    | Econdexp(e) ->
       Econdexp(expression e)
    | Econdpat(e, p) ->
       Econdpat(expression e, p)
    | Econdon(scpat, e) ->
       Econdon(scondpat scpat, expression e) in
  { scpat with desc = desc }
          

and expression ({ e_desc } as e) =
  let desc =
    match e_desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e_desc
    | Econstr1 { lname; arg_list } ->
       Econstr1 {lname; arg_list = List.map expression arg_list }
    | Eop(op, e_list) ->
       Eop(op, List.map expression e_list)
    | Etuple(e_list) -> Etuple(List.map expression e_list)
    | Elet({ l_eq } as leq, e) ->
       let l_eq, _ = equation l_eq in
       Elet({ leq with l_eq }, expression e)
    | Eapp(f, arg_list) ->
       Eapp(expression f, List.map expression arg_list)
    | Erecord_access({ label; arg }) ->
       Erecord_access({ label; arg = expression arg })
    | Erecord(le_list) ->
       let le_list =
         List.map (fun {label; arg} -> {label; arg = expression arg}) le_list in
       Erecord(le_list)
    | Erecord_with(e, le_list) ->
       let e = expression e in
       let le_list =
         List.map (fun {label; arg} -> {label; arg = expression arg}) le_list in
       Erecord_with(e, le_list)
    | Etypeconstraint(e, ty) ->
       Etypeconstraint(expression e, ty)
    | Efun(fd) -> Efun(funexp fd)
    | Ematch { is_total; e; handlers } ->
       let e = expression e in
       let handlers =
         List.map
           (fun ({ m_body } as m) -> { m with m_body = expression m_body })
           handlers in
       Ematch { is_total; e; handlers }
    | Epresent({ handlers; default_opt }) ->
       let handlers =
         List.map
           (fun ({ p_body } as p) -> { p with p_body = expression p_body })
           handlers in
       let default_opt =
         match default_opt with
         | NoDefault -> NoDefault
         | Init(e) -> Init(expression e)
         | Else(e) -> Else(expression e) in
       Epresent({ handlers; default_opt })
    | Ereset(e_body, e_res) ->
       Ereset(expression e_body, expression e_res) in
  { e with e_desc = desc }

and arg acc v_list = Util.mapfold vardec acc v_list
                   
and funexp ({ f_args; f_body } as fd) =
  let f_args, _ = Util.mapfold arg S.empty f_args in
  let f_body = result f_body in
  { fd with f_args = f_args; f_body = f_body }

and result ({ r_desc } as r) =
  let r_desc =
    match r_desc with
    | Exp(e) -> Exp(expression e)
    | Returns(b_eq) ->
       let b_eq, _, _ = block b_eq in
       Returns(b_eq) in
  { r with r_desc }
  
let implementation ({ desc } as i) =
  let desc = match desc with
    | Eopen _ -> desc
    | Eletdecl(f, e) -> Eletdecl(f, expression e)
    | Etypedecl _ -> desc in
  { i with desc = desc }
  
let program i_list = List.map implementation i_list
