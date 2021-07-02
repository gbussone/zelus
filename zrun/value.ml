(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Set of values *)
(* noinitialized and non causal values *)

type 'a extended =
  | Vnil : 'a extended
  | Vbot : 'a extended
  | Value : 'a -> 'a extended
  
type pvalue =
  | Vint : int -> pvalue
  | Vbool : bool -> pvalue
  | Vfloat : float -> pvalue
  | Vchar : char -> pvalue
  | Vstring : string -> pvalue
  | Vvoid : pvalue
  | Vconstr0 : Lident.t -> pvalue
  | Vconstr1 : Lident.t * value list -> pvalue
  | Vsconstr1 : Lident.t * pvalue list -> pvalue
  | Vrecord : pvalue Zelus.record list -> pvalue
  | Vtuple : value list -> pvalue
  | Vstuple : pvalue list -> pvalue
  | Vstate0 : Ident.t -> pvalue
  | Vstate1 : Ident.t * value list -> pvalue
  | Vclosure : Zelus.funexp * pvalue Ident.Env.t -> pvalue

and value = pvalue extended
          
and state =
  | Sempty : state
  | Stuple : state list -> state
  | Sval : value -> state
  | Sopt : value option -> state
                 
and ('a, 's, 'stop) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's, 'stop) Result.t } -> ('a, 's, 'stop) costream

and ('a, 'b, 's, 'stop) node =
  | CoFun  : ('a -> ('b, 'stop) Result.t) -> ('a, 'b, 's, 'stop) node
  | CoNode : { init : 's;
               step : 's -> 'a -> ('b * 's, 'stop) Result.t } ->
             ('a, 'b, 's, 'stop) node

type gvalue =
  | Gvalue : value -> gvalue
  | Gfun : (value, value, state, Error.kind) node -> gvalue

(* an input entry in the environment *)
type 'a ientry = { cur: 'a; default : 'a default }

and 'a default =
  | Val : 'a default
  | Last : 'a -> 'a default
  | Default : 'a -> 'a default
