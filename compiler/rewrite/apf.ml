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
  | EQinit _ -> failwith "EQinit"
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
  | [] -> Zaux.pmake (Econstpat Evoid) Deftypes.no_typ
  | [x] -> Zaux.pmake (Evarpat x) Deftypes.no_typ
  | x :: id_list ->
     Zaux.pairpat (Zaux.pmake (Evarpat x) Deftypes.no_typ)
       (pattern_of_list id_list)

let rec exp_of_list = function
  | [] -> Zaux.emake (Econst Evoid) Deftypes.no_typ
  | [x] -> Zaux.emake (Elocal x) Deftypes.no_typ
  | x :: id_list ->
     Zaux.pair (Zaux.emake (Elocal x) Deftypes.no_typ) (exp_of_list id_list)

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
  | Etypeconstraint _ -> failwith "Etypeconstraint"
  | Epresent _ -> failwith "Epresent"
  | Ematch _ -> failwith "Ematch"
  | Elet (l, e') ->
     let* l = local l in
     let* f, id_list = return_expression e' in
     return ((fun hole -> { e with e_desc = Elet (l, f hole) }), id_list)
  | Eseq _ -> failwith "Eseq"
  | Eperiod _ -> failwith "Eperiod"
  | Eblock _ -> failwith "Eblock"

let complete_params env id_list =
  let env =
    Zident.Env.filter
      (fun x _ -> List.for_all (fun x' -> Zident.compare x x' <> 0) id_list)
      env
  in
  Zident.Env.fold (fun x _ id_list -> x :: id_list) env []

let distribution_call fun_name e =
  Zaux.emake
    (Eapp (Zaux.prime_app,
           Zaux.emake
             (Zaux.global (Modname { qual = "Distribution"; id = fun_name }))
             Deftypes.no_typ,
           [e]))
    Deftypes.no_typ

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
                   Efundecl(n,
                            { body with f_kind = P;
                                        f_args =
                                          head
                                          @ [Zaux.pairpat
                                               (Zaux.pairpat pat1 pat2) tail];
                                        f_body = f e; f_env = f_env }) }
     :: { impl with desc =
                      Econstdecl (n ^ "_distributions",
                                  false,
                                  distribution_call "of_pair"
                                    (Zaux.pair dist1 dist2)) }
     :: acc

let implementation_list impl_list = Zmisc.fold implementation impl_list
