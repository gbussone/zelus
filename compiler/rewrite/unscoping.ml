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

let qualident { Lident.qual = qual; Lident.id = id } =
  { Zparsetree.qual = qual; Zparsetree.id = id }

let lident = function
  | Lident.Name n -> Zparsetree.Name n
  | Lident.Modname q -> Zparsetree.Modname (qualident q)

let zident = Zident.name

let immediate = function
  | Deftypes.Eint i -> Zparsetree.Eint i
  | Deftypes.Efloat f -> Zparsetree.Efloat f
  | Deftypes.Ebool b -> Zparsetree.Ebool b
  | Deftypes.Echar c -> Zparsetree.Echar c
  | Deftypes.Estring s -> Zparsetree.Estring s
  | Deftypes.Evoid -> Zparsetree.Evoid

let kind = function
  | Zelus.S -> Zparsetree.S
  | Zelus.A -> Zparsetree.A
  | Zelus.C -> Zparsetree.C
  | Zelus.D -> Zparsetree.D
  | Zelus.AD -> Zparsetree.AD
  | Zelus.AS -> Zparsetree.AS
  | Zelus.P -> Zparsetree.P

let localized f { Zelus.desc = desc; Zelus.loc = loc } =
  { Zparsetree.desc = f desc; Zparsetree.loc = loc }

let rec type_expression t = localized type_expression_desc t

and type_expression_desc = function
  | Zelus.Etypevar s -> Zparsetree.Etypevar s
  | Zelus.Etypeconstr (l, ts) ->
     Zparsetree.Etypeconstr (lident l, List.map type_expression ts)
  | Zelus.Etypetuple ts -> Zparsetree.Etypetuple (List.map type_expression ts)
  | Zelus.Etypevec (t, s) -> Zparsetree.Etypevec (type_expression t, size s)
  | Zelus.Etypefun (k, z_opt, t1, t2) ->
     Zparsetree.Etypefun (kind k,
                          Option.map zident z_opt,
                          type_expression t1,
                          type_expression t2)

and size s = localized size_desc s

and size_desc = function
  | Zelus.Sconst i -> Zparsetree.Sconst i
  | Zelus.Sglobal l -> Zparsetree.Sname (lident l)
  | Zelus.Sname z -> Zparsetree.Sname (Zparsetree.Name (zident z))
  | Zelus.Sop (s_op, s1, s2) -> Zparsetree.Sop (size_op s_op, size s1, size s2)

and size_op = function
  | Zelus.Splus -> Zparsetree.Splus
  | Zelus.Sminus -> Zparsetree.Sminus

let rec interface i = localized interface_desc i

and interface_desc = function
  | Zelus.Einter_open _
  | Zelus.Einter_typedecl (_, _, _)
  | Zelus.Einter_constdecl (_, _) -> assert false

and type_decl t = localized type_decl_desc t

and type_decl_desc = function
  | Zelus.Eabstract_type -> Zparsetree.Eabstract_type
  | Zelus.Eabbrev t -> Zparsetree.Eabbrev (type_expression t)
  | Zelus.Evariant_type cs ->
     Zparsetree.Evariant_type (List.map constr_decl cs)
  | Zelus.Erecord_type sts ->
     Zparsetree.Erecord_type
       (List.map (fun (s, t) -> s, type_expression t) sts)

and constr_decl c = localized constr_decl_desc c

and constr_decl_desc = function
  | Zelus.Econstr0decl s -> Zparsetree.Econstr0decl s
  | Zelus.Econstr1decl (s, ts) ->
     Zparsetree.Econstr1decl (s, List.map type_expression ts)

and implementation i = localized implementation_desc i

and implementation_desc = function
  | Zelus.Eopen s -> Zparsetree.Eopen s
  | Zelus.Etypedecl (s, ss, t) -> Zparsetree.Etypedecl (s, ss, type_decl t)
  | Zelus.Econstdecl (s, b, e) -> Zparsetree.Econstdecl (s, b, exp e)
  | Zelus.Efundecl (s, f) -> Zparsetree.Efundecl (s, funexp f)

and funexp
    { Zelus.f_kind = f_kind;
      Zelus.f_atomic = f_atomic;
      Zelus.f_args = f_args;
      Zelus.f_body = f_body;
      Zelus.f_loc = f_loc } =
  { Zparsetree.f_kind = kind f_kind;
    Zparsetree.f_atomic = f_atomic;
    Zparsetree.f_args = List.map pattern f_args;
    Zparsetree.f_body = exp f_body;
    Zparsetree.f_loc = f_loc }

and exp { Zelus.e_desc = e_desc; Zelus.e_loc = e_loc } =
  { Zparsetree.desc = desc e_desc; Zparsetree.loc = e_loc }

and desc = function
  | Zelus.Elocal z -> Zparsetree.Evar (Name (zident z))
  | Zelus.Eglobal { lname = lname } -> Zparsetree.Evar (lident lname)
  | Zelus.Econst i -> Zparsetree.Econst (immediate i)
  | Zelus.Econstr0 l -> Zparsetree.Econstr0 (lident l)
  | Zelus.Econstr1 (l, es) -> Zparsetree.Econstr1 (lident l, List.map exp es)
  | Zelus.Elast z -> Zparsetree.Elast (zident z)
  | Zelus.Eapp (a, e, es) -> Zparsetree.Eapp (app a, exp e, List.map exp es)
  | Zelus.Eop (o, es) -> Zparsetree.Eop (op o, List.map exp es)
  | Zelus.Etuple es -> Zparsetree.Etuple (List.map exp es)
  | Zelus.Erecord_access (e, l) -> Zparsetree.Erecord_access (exp e, lident l)
  | Zelus.Erecord les ->
     Zparsetree.Erecord (List.map (fun (l, e) -> lident l, exp e) les)
  | Zelus.Erecord_with (e, les) ->
     Zparsetree.Erecord_with (exp e,
                              List.map (fun (l, e) -> lident l, exp e) les)
  | Zelus.Etypeconstraint (e, t) ->
     Zparsetree.Etypeconstraint (exp e, type_expression t)
  | Zelus.Epresent (_, _) -> assert false
  | Zelus.Ematch (_, e, e_mhs) ->
     Zparsetree.Ematch (exp e, List.map (match_handler exp) e_mhs)
  | Zelus.Elet (l, e) ->
     let b, es = (local l).Zparsetree.desc in
     Zparsetree.Elet (b, es, exp e)
  | Zelus.Eseq (e1, e2) -> Zparsetree.Eseq (exp e1, exp e2)
  | Zelus.Eperiod p -> Zparsetree.Eperiod (period p)
  | Zelus.Eblock (b, e) -> Zparsetree.Eblock (block b, exp e)

and op = function
  | Zelus.Efby -> Zparsetree.Efby
  | Zelus.Eunarypre -> Zparsetree.Eunarypre
  | Zelus.Eifthenelse -> Zparsetree.Eifthenelse
  | Zelus.Eminusgreater -> Zparsetree.Eminusgreater
  | Zelus.Eup -> Zparsetree.Eup
  | Zelus.Einitial -> Zparsetree.Einitial
  | Zelus.Edisc -> Zparsetree.Edisc
  | Zelus.Ehorizon -> assert false
  | Zelus.Etest -> Zparsetree.Etest
  | Zelus.Eaccess -> Zparsetree.Eaccess
  | Zelus.Eupdate -> Zparsetree.Eupdate
  | Zelus.Eslice (s1, s2) -> Zparsetree.Eslice (size s1, size s2)
  | Zelus.Econcat -> Zparsetree.Econcat
  | Zelus.Eatomic -> Zparsetree.Eatomic

and app
    { Zelus.app_inline = app_inline; Zelus.app_statefull = app_statefull } =
  { Zparsetree.app_inline = app_inline;
    Zparsetree.app_statefull = app_statefull }

and period { Zelus.p_phase = p_phase; Zelus.p_period = p_period } =
  { Zparsetree.p_phase = Option.map exp p_phase;
    Zparsetree.p_period = exp p_period }

and pattern { Zelus.p_desc = p_desc; Zelus.p_loc = p_loc } =
  { Zparsetree.desc = pdesc p_desc; Zparsetree.loc = p_loc }

and pdesc = function
  | Zelus.Ewildpat -> Zparsetree.Ewildpat
  | Zelus.Econstpat i -> Zparsetree.Econstpat (immediate i)
  | Zelus.Econstr0pat l -> Zparsetree.Econstr0pat (lident l)
  | Zelus.Econstr1pat (l, ps) ->
     Zparsetree.Econstr1pat (lident l, List.map pattern ps)
  | Zelus.Etuplepat ps -> Zparsetree.Etuplepat (List.map pattern ps)
  | Zelus.Evarpat z -> Zparsetree.Evarpat (zident z)
  | Zelus.Ealiaspat (p, z) -> Zparsetree.Ealiaspat (pattern p, zident z)
  | Zelus.Eorpat (p1, p2) -> Zparsetree.Eorpat (pattern p1, pattern p2)
  | Zelus.Erecordpat lps ->
     Zparsetree.Erecordpat (List.map (fun (l, p) -> lident l, pattern p) lps)
  | Zelus.Etypeconstraintpat (p, t) ->
     Zparsetree.Etypeconstraintpat (pattern p, type_expression t)

and eq { Zelus.eq_desc = eq_desc; Zelus.eq_loc = eq_loc } =
  { Zparsetree.desc = eqdesc eq_desc; Zparsetree.loc = eq_loc }

and eqdesc = function
  | Zelus.EQeq (p, e) -> Zparsetree.EQeq (pattern p, exp e)
  | Zelus.EQder (z, e, e_opt, e_phs) ->
     Zparsetree.EQder (zident z,
                       exp e,
                       Option.map exp e_opt,
                       List.map (present_handler exp) e_phs)
  | Zelus.EQinit (z, e) -> Zparsetree.EQinit (zident z, exp e)
  | Zelus.EQnext (z, e, e_opt) ->
     Zparsetree.EQnext (zident z, exp e, Option.map exp e_opt)
  | Zelus.EQpluseq (z, e) -> Zparsetree.EQpluseq (zident z, exp e)
  | Zelus.EQautomaton (_, shs, s_opt) ->
     Zparsetree.EQautomaton (List.map state_handler shs,
                             Option.map state_exp s_opt)
  | Zelus.EQpresent (b_phs, b_opt) ->
     Zparsetree.EQpresent (List.map (present_handler block) b_phs,
                           Option.map block b_opt)
  | Zelus.EQmatch (_, e, b_mhs) ->
     Zparsetree.EQmatch (exp e, List.map (match_handler block) b_mhs)
  | Zelus.EQreset (es, e) -> Zparsetree.EQreset (List.map eq es, exp e)
  | Zelus.EQemit (z, e_opt) ->
     Zparsetree.EQemit (zident z, Option.map exp e_opt)
  | Zelus.EQblock b -> Zparsetree.EQblock (block b)
  | Zelus.EQand es -> Zparsetree.EQand (List.map eq es)
  | Zelus.EQbefore es -> Zparsetree.EQbefore (List.map eq es)
  | Zelus.EQforall fh -> Zparsetree.EQforall (forall_handler fh)

and block
    { Zelus.b_vars = b_vars;
      Zelus.b_locals = b_locals;
      Zelus.b_body = b_body;
      Zelus.b_loc = b_loc } =
  { Zparsetree.desc =
      { Zparsetree.b_vars = List.map vardec b_vars;
        Zparsetree.b_locals = List.map local b_locals;
        Zparsetree.b_body = List.map eq b_body };
    Zparsetree.loc = b_loc }

and vardec
    { Zelus.vardec_name = vardec_name;
      Zelus.vardec_default = vardec_default;
      Zelus.vardec_combine = vardec_combine;
      Zelus.vardec_loc = vardec_loc } =
  { Zparsetree.desc =
      { Zparsetree.vardec_name = zident vardec_name;
        Zparsetree.vardec_default = Option.map default vardec_default;
        Zparsetree.vardec_combine = Option.map lident vardec_combine };
    Zparsetree.loc = vardec_loc }

and default = function
  | Zelus.Init _
  | Zelus.Default _ -> assert false

and local { Zelus.l_rec = l_rec; Zelus.l_eq = l_eq; Zelus.l_loc = l_loc } =
  { Zparsetree.desc = l_rec, List.map eq l_eq; Zparsetree.loc = l_loc }

and state_handler { Zelus.s_loc; Zelus.s_state; Zelus.s_body; Zelus.s_trans; Zelus.s_env; Zelus.s_reset } = assert false

and statepat s = localized statepatdesc s

and statepatdesc = function
  | Zelus.Estate0pat _
  | Zelus.Estate1pat (_, _) -> assert false

and state_exp s = localized state_exdesc s

and state_exdesc = function
  | Zelus.Estate0 _
  | Zelus.Estate1 (_, _) -> assert false

and escape { Zelus.e_cond; Zelus.e_reset; Zelus.e_block; Zelus.e_next_state; Zelus.e_env; Zelus.e_zero } = assert false

and scondpat s = localized scondpat_desc s

and scondpat_desc = function
  | Zelus.Econdand (_, _)
  | Zelus.Econdor (_, _)
  | Zelus.Econdexp _
  | Zelus.Econdpat (_, _)
  | Zelus.Econdon (_, _) -> assert false

and match_handler : type a b. (a -> b) -> a Zelus.match_handler -> b Zparsetree.match_handler = fun f { Zelus.m_pat; Zelus.m_body; Zelus.m_env; Zelus.m_reset; Zelus.m_zero } -> assert false

and present_handler : type a b. (a -> b) -> a Zelus.present_handler -> b Zparsetree.present_handler = fun f { Zelus.p_cond; Zelus.p_body; Zelus.p_env; Zelus.p_zero } -> assert false

and forall_handler { Zelus.for_index; Zelus.for_init; Zelus.for_body; Zelus.for_in_env; Zelus.for_out_env; Zelus.for_loc } = assert false

and indexes_desc = function
  | Zelus.Einput (_, _)
  | Zelus.Eoutput (_, _)
  | Zelus.Eindex (_, _, _) -> assert false

and init_desc = function
  | Zelus.Einit_last (_, _) -> assert false

let implementation_list impl_list = Zmisc.iter implementation impl_list
