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

open Zelus

(*
(* translation of a probabilistic node into a node. *)
(* the translation is applied to normalised programs *)

(* every probabilistic node:
   
   [let proba f x1 ... xn = ...]

is translated into:

   [let node f x1 ... prob xn = ...]

and every application of a probabilistic node:

   [f e1 ... en]

into:

   [f e1 ... prob en]
 *)

open Zelus
open Deftypes
open Lident
open Zident
       
let new_prob () = Zident.fresh "prob"

(* If the extra parameter [prob] is given a type, say [prob] *)
(* this type but be bind to an actual module or interface. This makes *)
(* the translation dependent on the infer function. This is why we *)
(* chose to give it a type variable. *)
let typ_prob = Ztypes.make (Deftypes.Tvar)
let prob_varpat x = Zaux.varpat x typ_prob
let prob_var x = Zaux.var x typ_prob
							  
(* Add the extra input parameter "time" for hybrid nodes *)
let extra_input prob env = 
  Env.add prob { t_sort = Deftypes.value; t_typ = typ_prob } env,
  (prob_varpat prob)

(** Translation of expressions. *)
let rec expression prob ({ e_desc = e_desc } as e) =
  match e_desc with
  | Eperiod({ p_phase = opt_p1; p_period = p2 }) ->
     { e with e_desc =
		Eperiod({ p_phase =
			    Zmisc.optional_map (expression prob) opt_p1;
			  p_period = expression prob p2 }) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (expression prob) e_list) }
  | Eapp(app, op, e_list) ->
     let op = expression prob op in
     let e_list = List.map (expression prob) e_list in
     let e_list =
       if Ztypes.is_probabilistic (List.length e_list - 1) op.e_typ then
         let head, tail = Zmisc.firsts e_list in
         head @ [Zaux.pair (prob_var prob) tail]
       else e_list in
     { e with e_desc = Eapp(app, op, e_list) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression prob) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression prob) e_list) }
  | Erecord_access(e_record, x) ->
     { e with e_desc = Erecord_access(expression prob e_record, x) }
  | Erecord(l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression prob e)) l_e_list in
     { e with e_desc = Erecord(l_e_list) }
  | Erecord_with(e_record, l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression prob e)) l_e_list in
     { e with e_desc = Erecord_with(expression prob e_record, l_e_list) }
  | Etypeconstraint(e, ty) ->
     { e with e_desc = Etypeconstraint(expression prob e, ty) }
  | Elet(l, e) ->
     { e with e_desc = Elet(local prob l, expression prob e) }
  | Eblock(b, e) ->
     { e with e_desc = Eblock(block prob b, expression prob e) }
  | Eseq(e1, e2) ->
     { e with e_desc =
		Eseq(expression prob e1, expression prob e2) }
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Epresent _ | Ematch _ -> assert false

(* Translation of equations *)
and equation prob ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression prob e) }
  | EQpluseq(x, e) -> { eq with eq_desc = EQpluseq(x, expression prob e) }
  | EQmatch(total, e, m_h_list) ->
     let m_h_list =
       List.map
         (fun ({ m_body = b } as m_h) ->
	  { m_h with m_body = block prob b })
	 m_h_list in
     { eq with eq_desc = EQmatch(total, expression prob e, m_h_list) }
  | EQreset(res_eq_list, e) ->
     let e = expression prob e in
     let res_eq_list = equation_list prob res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list prob and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc = EQbefore(equation_list prob before_eq_list) }
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression prob e) }
  | EQder(x, e, None, []) -> 
     { eq with eq_desc = EQder(x, expression prob e, None, []) }
  | EQnext(x, e, e_opt) ->
     let e_opt = Zmisc.optional_map (expression prob) e_opt in
     { eq with eq_desc = EQnext(x, expression prob e, e_opt) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block prob b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
       | Einput(x, e) -> Einput(x, expression prob e)
       | Eoutput _ -> desc
       | Eindex(x, e1, e2) ->
	  Eindex(x, expression prob e1, expression prob e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, expression prob e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block prob b_eq_list in
     { eq with eq_desc = EQforall { body with for_index = i_list;
					      for_init = init_list;
					      for_body = b_eq_list } }
  | EQautomaton _ | EQpresent _ | EQemit _
  | EQder _ -> assert false
		      
and equation_list prob eq_list = List.map (equation prob) eq_list
					  
(** Translate a block *)
and block prob ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map (local prob) l_list in
  let eq_list = equation_list prob eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local prob ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list prob eq_list }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | AS | A | AD | D | C) }) -> impl
  | Efundecl(n, ({ f_kind = P; f_args = pat_list;
		   f_body = e; f_env = f_env } as body)) ->
     let prob = new_prob () in
     let e = expression prob e in
     let head, tail = Zmisc.firsts pat_list in
     let f_env, prob = extra_input prob f_env in
     { impl with desc = 
		   Efundecl(n,
			    { body with f_kind = D;
					f_args =
					  head @ [Zaux.pairpat prob tail]; 
					f_body = e; f_env = f_env }) }
  *)

let union env1 env2 =
  Zident.Env.union
    (fun _ _ _ -> failwith "init sample is used twice with the same name")
    env1 env2

let return x = x, Zident.Env.empty
let bind e f =
  let x, env1 = e in
  let y, env2 = f x in
  y, union env1 env2
let ( let* ) = bind

let rec map f = function
  | [] -> return []
  | x :: xs ->
     let* y = f x in
     let* ys = map f xs in
     return (y :: ys)

let rec filter_map f = function
  | [] -> return []
  | x :: xs ->
     let* y_opt = f x in
     let* ys = filter_map f xs in
     match y_opt with
     | None -> return ys
     | Some y -> return (y :: ys)

let pmake desc = Zaux.pmake desc Deftypes.no_typ
let emake desc = Zaux.emake desc Deftypes.no_typ

let rec expression ({ e_desc = e_desc } as e) =
  match e_desc with
  | Elocal _ -> return e
  | Eglobal _ -> return e
  | Econst _ -> return e
  | Econstr0 _ -> return e
  | Econstr1 (c, e_list) ->
     let* e_list = map expression e_list in
     return { e with e_desc = Econstr1 (c, e_list) }
  | Elast _ -> return e
  | Eapp (app, op, e_list) ->
     let* op = expression op in
     let* e_list = map expression e_list in
     return { e with e_desc = Eapp (app, op, e_list) }
  | Eop (op, e_list) ->
     let* e_list = map expression e_list in
     return { e with e_desc = Eop (op, e_list) }
  | Etuple e_list ->
     let* e_list = map expression e_list in
     return { e with e_desc = Etuple e_list }
  | Erecord_access (e_record, x) ->
     let* e_record = expression e_record in
     return { e with e_desc = Erecord_access (e_record, x) }
  | Erecord l_e_list ->
     let* l_e_list =
       map
         (fun (l, e) ->
            let* e = expression e in
            return (l, e))
         l_e_list
     in
     return { e with e_desc = Erecord l_e_list }
  | Erecord_with (e_record, l_e_list) ->
     let* e_record = expression e_record in
     let* l_e_list =
       map
         (fun (l, e) ->
            let* e = expression e in
            return (l, e))
         l_e_list
     in
     return { e with e_desc = Erecord_with (e_record, l_e_list) }
  | Etypeconstraint (e', ty) ->
     let* e' = expression e' in
     return { e with e_desc = Etypeconstraint (e', ty) }
  | Epresent _ -> failwith "Epresent"
  | Ematch _ -> failwith "Ematch"
  | Elet (l, e') ->
     let* l = local l in
     let* e' = expression e' in
     return { e with e_desc = Elet (l, e') }
  | Eseq (e1, e2) ->
     let* e1 = expression e1 in
     let* e2 = expression e2 in
     return { e with e_desc = Eseq (e1, e2) }
  | Eperiod _ -> failwith "Eperiod"
  | Eblock (b, e') ->
     let* b = block b in
     let* e' = expression e' in
     return { e with e_desc = Eblock (b, e') }

and equation ({ eq_desc = eq_desc } as eq) =
  match eq_desc with
  | EQeq (p, e) ->
     let* e = expression e in
     return (Some { eq with eq_desc = EQeq (p, e) })
  | EQder _ -> failwith "EQder"
  | EQinit (x,
            { e_desc =
                Eapp (_,
                      { e_desc = Eglobal { lname = Name "sample" } },
                      [e]) }) ->
     None, Zident.Env.singleton x e
  | EQinit (x, e) ->
     let* e = expression e in
     return (Some { eq with eq_desc = EQinit (x, e) })
  | EQnext _ -> failwith "EQnext"
  | EQpluseq _ -> failwith "EQpluseq"
  | EQautomaton _ -> failwith "EQautomaton"
  | EQpresent _ -> failwith "EQpresent"
  | EQmatch _ -> failwith "EQmatch"
  | EQreset _ -> failwith "EQreset"
  | EQemit _ -> failwith "EQemit"
  | EQblock _ -> failwith "EQblock"
  | EQand _ -> failwith "EQand"
  | EQbefore _ -> failwith "EQbefore"
  | EQforall _ -> failwith "EQforall"

and block ({ b_locals = l_list; b_body = eq_list } as b) =
  let* l_list = map local l_list in
  let* eq_list = filter_map equation eq_list in
  return { b with b_locals = l_list; b_body = eq_list }

and local ({ l_eq = eq_list } as l) =
  let* eq_list = filter_map equation eq_list in
  return { l with l_eq = eq_list }

let rec pattern_of_list = function
  | [] -> pmake (Econstpat Evoid)
  | [x] -> pmake (Evarpat x)
  | x :: id_list -> Zaux.pairpat (pmake (Evarpat x)) (pattern_of_list id_list)

let rec exp_of_list = function
  | [] -> emake (Econst Evoid)
  | [x] -> emake (Elocal x)
  | x :: id_list -> Zaux.pair (emake (Elocal x)) (exp_of_list id_list)

let params ({ e_desc = e_desc } as e) =
  let rec aux { e_desc = e_desc } =
    match e_desc with
    | Elocal x -> [x]
    | Etuple [{ e_desc = Elocal x }; e2] ->
       let id_list = aux e2 in
       assert (List.for_all (fun x' -> Zident.compare x x' <> 0) id_list);
       x :: id_list
    | _ -> failwith "Too complex"
  in
  match e_desc with
  | Econst Evoid -> []
  | _ -> aux e

let rec return_expression ({ e_desc = e_desc } as e) =
  match e_desc with
  | Elocal _ -> failwith "Elocal"
  | Eglobal _ -> failwith "Eglobal"
  | Econst _ -> failwith "Econst"
  | Econstr0 _ -> failwith "Econstr0"
  | Econstr1 _ -> failwith "Econstr1"
  | Elast _ -> failwith "Elast"
  | Eapp _ -> failwith "Eapp"
  | Eop _ -> failwith "Eop"
  | Etuple [e1; e2] ->
     let id_list = params e1 in
     let* e2 = expression e2 in
     return
       ((fun hole ->
           { e with e_desc =
                      Etuple [{ e1 with e_desc = Etuple [e1; hole] }; e2] }),
        id_list)
  | Etuple _ -> failwith "Etuple"
  | Erecord_access _ -> failwith "Erecord_access"
  | Erecord _ -> failwith "Erecord"
  | Erecord_with _ -> failwith "Erecord_with"
  | Etypeconstraint (e', ty) ->
     let* f, id_list = return_expression e' in
     return
       ((fun hole -> { e with e_desc = Etypeconstraint (f hole, ty) }),
        id_list)
  | Epresent _ -> failwith "Epresent"
  | Ematch _ -> failwith "Ematch"
  | Elet (l, e') ->
     let* l = local l in
     let* f, id_list = return_expression e' in
     return ((fun hole -> { e with e_desc = Elet (l, f hole) }), id_list)
  | Eseq (e1, e2) ->
     let* e1 = expression e1 in
     let* f, id_list = return_expression e2 in
     return ((fun hole -> { e with e_desc = Eseq (e1, f hole) }), id_list)
  | Eperiod _ -> failwith "Eperiod"
  | Eblock (b, e') ->
     let* b = block b in
     let* f, id_list = return_expression e' in
     return ((fun hole -> { e with e_desc = Eblock (b, f hole) }), id_list)

let complete_params env id_list =
  let env =
    Zident.Env.filter
      (fun x _ -> List.for_all (fun x' -> Zident.compare x x' <> 0) id_list)
      env
  in
  Zident.Env.fold (fun x _ id_list -> x :: id_list) env []

let distribution_call fun_name e =
  emake
    (Eapp (Zaux.prime_app,
           emake
             (Zaux.global (Modname { qual = "Distribution"; id = fun_name })),
           [e]))

let rec dist_of_list env = function
  | [] -> distribution_call "dirac" Zaux.evoid
  | [x] -> Zident.Env.find x env
  | x :: id_list ->
     distribution_call "of_pair"
       (Zaux.pair (Zident.Env.find x env) (dist_of_list env id_list))

let implementation acc impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl (_, { f_kind = (S | AS | A | AD | D | C) }) -> impl :: acc
  | Efundecl (n, ({ f_kind = P; f_args = pat_list;
                    f_body = e; f_env = f_env } as body)) ->
     let (f, id_list1), env = return_expression e in
     let pat1 = pattern_of_list id_list1 in
     let dist1 = dist_of_list env id_list1 in
     let id_list2 = complete_params env id_list1 in
     let pat2 = pattern_of_list id_list2 in
     let dist2 = dist_of_list env id_list2 in
     let e = exp_of_list id_list2 in
     let head, tail = Zmisc.firsts pat_list in
     { impl with desc =
                   Econstdecl (n,
                               false,
                               Zaux.pair
                                 (emake (Zaux.global (Name ("__" ^ n))))
                                 (distribution_call "of_pair"
                                    (Zaux.pair dist1 dist2))) }
     :: { impl with desc =
                      Efundecl("__" ^ n,
                               { body with f_kind = P;
                                           f_args =
                                             head
                                             @ [Zaux.pairpat
                                                  (Zaux.pairpat pat1 pat2)
                                                  tail];
                                           f_body = f e; f_env = f_env }) }
     :: acc

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
          ({ e_desc = Eglobal { lname = Name "infer" } } as op),
          [e1; ({ e_desc = Etuple [e21; e22] } as e2)]) ->
    { e with
      e_desc =
        Eapp (app,
              op,
              [e1;
               { e2 with
                 e_desc =
                   Etuple [emake (Eapp (Zaux.prime_app,
                                        emake (Zaux.global (Name "mk_model")),
                                        [e21]));
                           e22] }]) }
  | Eapp (app,
          ({ e_desc = Eglobal
                 { lname = Modname { qual = modname; id = "infer" } } } as op),
          [e1; ({ e_desc = Etuple [e21; e22] } as e2)]) ->
    { e with
      e_desc =
        Eapp (app,
              op,
              [e1;
               { e2 with
                 e_desc =
                   Etuple [emake (Eapp (Zaux.prime_app,
                                        emake (Zaux.global
                                                 (Modname
                                                    { qual = modname;
                                                      id = "mk_model" })),
                                        [e21]));
                           e22] }]) }
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

let implementation2 impl =
  match impl.desc with
  | Eopen _ -> impl
  | Etypedecl _ -> impl
  | Econstdecl (n, static, e) ->
     { impl with desc = Econstdecl (n, static, expression e) }
  | Efundecl (n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl (n, { body with f_body = expression e }) }

let implementation_list impl_list = Zmisc.fold implementation (List.map implementation2 impl_list)
