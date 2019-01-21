open Ztypes
open Symbolic


type pstate = {
  mutable env : env
}

let gen_id =
  let cpt = ref 0 in
  fun () ->
    incr cpt;
    !cpt

let sample (pstate, (ef, natural_params)) =
  let id = gen_id () in
  pstate.env <- (id, (ef, natural_params)) :: pstate.env;
  Var id

let rec zip lst1 lst2 = match lst1,lst2 with
  | [],_ -> []
  | _, []-> []
  | (x::xs),(y::ys) -> (x,y) :: zip xs ys

let assoc_update i v' =
  List.map (fun (k, v) -> (k, if i = k then v' else v))

let analytic_update =
  let rec updater x f = function
    | [] -> None
    | (a, b) :: ys -> if x = a
      then Some (f b :: List.map snd ys)
      else option_map (List.cons b) (updater x f ys)
  in fun (mx, mp) -> match IntMap.bindings mp with
    | [] -> fun env -> Some env
    | [(i, e)] -> fun env -> (match List.assoc_opt i env with
      | Some (ef, natural_params) ->
        let to_add = match mx with
          | Some x -> x
          | None -> 1.
        in
        (match updater e (fun z -> z +. to_add)
          (zip ef.suff_stats natural_params) with
          | Some natural_params' -> Some (assoc_update i (ef, natural_params') env)
          | None -> None)
      | None -> None)
    | i :: j :: xs -> fun env -> None

let mc_update env exp =
  assert false (* XXX TODO XXX *)

let rec apply_all f = function
  | [] -> fun e -> Some e
  | x :: xs -> fun e -> match f x e with
    | None -> None
    | Some e' -> apply_all f xs e'

let factor (pstate, exp) =
  let analytic =
    begin match map_option_list variable_representation (get_sum_of_prod exp) with
      | None -> None
      | Some xs -> apply_all analytic_update xs pstate.env
    end
  in
  begin match analytic with
    | Some env' -> pstate.env <- env'
    | None -> pstate.env <- mc_update pstate.env exp
  end

(* let node infer model i = (env, o) where *)
(*     rec env, o =  model ([] fby env, i) *)

type 'a infer_state =
  { infer_nstate : 'a;
    infer_pstate : pstate; }

let infer (Node { alloc; reset; step; }) =
  let alloc () =
    { infer_nstate = alloc();
      infer_pstate = { env = Symbolic.empty_env; }; }
  in
  let reset state =
    reset state.infer_nstate;
    state.infer_pstate.env <- empty_env
  in
  let step state i =
    let o = step state.infer_nstate (state.infer_pstate, i) in
    state.infer_pstate.env, o
  in
  Node { alloc; reset; step; }
