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

let implementation_list impl_list =
  let modules = Modules.modules in
  let modules = modules.modules in
  Modules.E.iter
    (fun modname env ->
       let values = env.Modules.values in
       let value_desc = Modules.E.find "infer" values in
       let value_typ = value_desc.value_typ in
       let typ_vars = value_typ.typ_vars in
       let typ_body = value_typ.typ_body in
       let t_desc = typ_body.t_desc in
       match t_desc with
       | Tfun (_, _, _, { t_desc = Tfun (_, _, ({ t_desc = Tfun (Tproba, None, alpha, { t_desc = Tproduct [beta; gamma] }) } as t1), ({ t_desc = Tfun (Tdiscrete true, None, alpha', t14) } as t2)) }) when alpha = alpha' ->
         Zmisc.push_binding_level ();
         let delta = Ztypes.new_var () in
         Zmisc.pop_binding_level ();
         t1.t_desc <- Tfun (Tproba, None, Deftypes.make (Deftypes.Tproduct [Deftypes.make (Deftypes.Tproduct [beta; delta]); alpha]), gamma);
         t2.t_desc <- Tfun (Tdiscrete true, None, Deftypes.make (Deftypes.Tproduct [Deftypes.make (Deftypes.Tconstr ({ qual = "Distribution"; id = "t" }, [Deftypes.make (Deftypes.Tproduct [beta; delta])], Deftypes.no_abbrev ())); alpha]), t14);
         value_desc.value_typ <- { value_typ with typ_vars = delta :: typ_vars }
       | _ -> assert false)
    modules;
  impl_list
