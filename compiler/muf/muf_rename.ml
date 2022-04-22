open Muf

let freshname =
  Muf_utils.fresh

let rec rename_patt :
  type a. (identifier, identifier) Hashtbl.t -> a pattern -> a pattern = begin
  fun tbl p ->
    let patt =
      begin match p.patt with
      | Pid x ->
        begin match Hashtbl.find_opt tbl x with
        | Some n -> Pid n
        | None ->
          let new_name = freshname x.name in
          let _ = Hashtbl.add tbl x new_name in
          Pid new_name
        end
      | Pany
      | Pconst _
      | Ptuple _
      | Ptype _
      | Pconstr _ -> map_patt_desc (rename_patt tbl) p.patt
      end
    in { p with patt = patt }
  end

let rec rename_expr :
  type a. a expression -> (identifier, identifier) Hashtbl.t -> a expression = begin
  fun e tbl ->
    let get_name n =
      let n =
        begin match Hashtbl.find_opt tbl n with
        | None -> n (* free variable, etc *)
        | Some n -> n
        end
      in n
    in
    let rec hide p tbl =
      begin match p.patt with
      | Pany | Pconst _-> ()
      | Pid x -> Hashtbl.add tbl x x
      | Ptuple l -> List.iter (fun patt -> hide patt tbl) l
      | Ptype (p, _) -> hide p tbl
      | Pconstr _ -> assert false
      end
    in
    let rec restore p tbl =
      begin match p.patt with
      | Pany | Pconst _-> ()
      | Pid x -> Hashtbl.remove tbl x
      | Ptuple l -> List.iter (fun patt -> restore patt tbl) l
      | Ptype (p, _) -> restore p tbl
      | Pconstr _ -> assert false
      end
    in
    let rec rename e =
      let expr =
        begin match e.expr with
        | Evar n ->
          let n = get_name n in
          Evar n
        | Elet(p, e1, e2) ->
          let e1 = rename e1 in
          hide p tbl;
          let e2 = rename_expr e2 tbl in
          restore p tbl;
          Elet(p, e1, e2)
        | Esample (prob, e) ->
          let prob = get_name  { modul = None; name = prob } in
          let e = rename e in
          Esample(prob.name, e)
        | Eobserve (prob, e1, e2) ->
          let prob = get_name  { modul = None; name = prob } in
          let e1 = rename e1 in
          let e2 = rename e2 in
          Eobserve(prob.name, e1, e2)
        | Efactor (prob, e) ->
          let prob = get_name  { modul = None; name = prob } in
          let e = rename e in
          Efactor (prob.name, e)
        | Einfer (e, n) ->
          let n = get_name n in
          let e = rename e in
          Einfer(e, n)
        | Econst _
        | Efield _
        | Eapp _
        | Eif _
        | Esequence _
        | Ecall_init _
        | Ecall_step _
        | Ecall_reset _
        | Etuple _
        | Econstr _ (* Econstr (identifier, _) : the identifier here is a constructor name *)
        | Efun _
        | Erecord _ ->
          map_expr_desc (fun p -> p) rename e.expr
        | Ematch _ -> assert false
        end
      in { e with expr=expr }
    in rename e
  end

let rec compile_expr :
  type a. a expression -> a expression = begin
    fun e ->
      let expr =
        begin match e.expr with
        | Elet(p, e1, e2) ->
          let e1 = compile_expr e1 in
          let tbl = (Hashtbl.create 100) in
          let p = rename_patt tbl p in
          let e2 = compile_expr (rename_expr e2 tbl) in
          Elet(p, e1, e2)
        | Econst _
        | Evar _
        | Efield _
        | Eapp _
        | Eif _
        | Esequence _
        | Ecall_init _
        | Ecall_step _
        | Esample _
        | Eobserve _
        | Efactor _
        | Einfer _
        | Etuple  _
        | Erecord _
        | Econstr _
        | Efun _
        | Ecall_reset _ ->
          map_expr_desc (fun p -> p) compile_expr e.expr
        | Ematch _ -> assert false
        end
      in { e with expr=expr }
    end


let compile_node :
  type a. (a pattern, a expression) decl_desc -> (a pattern, a expression) decl_desc = begin
    fun d ->
      begin match d with
      | Dnode (f, params, n) ->
        let n' =
          let compile_method_with_params (p, e) = (p, compile_expr e) in
          let compile_class n =
            let ei = compile_expr n.n_init in
            let ps, es = compile_method_with_params n.n_step in
            {n with n_init = ei ; n_step = (ps, es)}
          in compile_class n
        in Dnode(f, params, n')
      | _ -> d
    end
  end

let compile_decl :
  type a. a declaration ->  a declaration = begin
    fun d ->
      let decl =
      begin match d.decl with
      | Ddecl (p, e) ->
        let e = compile_expr e in
        Ddecl(p, e)
      | Dfun (f, p, e) ->
        let e = compile_expr e in
        Dfun (f, p, e)
      | Dnode (f, p, n) as dn -> compile_node dn
      | Dtype _ | Dopen _ -> d.decl
      end
    in {decl}
  end

let compile_program :
  type a. a program -> a program = begin
    fun p ->
      let p = List.map compile_decl p in
      p
  end
