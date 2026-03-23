open Base
open Ast

let todo () = failwith "TODO"

(* Shadow the Base version of common list functions *)
let map = Stdlib.List.map
let fold_left = Stdlib.List.fold_left
let fold_right = Stdlib.List.fold_right
let filter = Stdlib.List.filter

exception Type_error of string

let ty_err msg = raise (Type_error msg)

(**********************************************
  *         Typing Environment (Gamma)        *
  *********************************************)

type gamma = (string * ty) list [@@deriving equal, compare, show]
(** Gamma is the type environment that maps variables to types *)

let uncurry f (x, y) = f x y

(** Pretty-printer for gamma *)
let pp_gamma : gamma Fmt.t =
    let open Fmt in
    let pp_pair = hbox (pair ~sep:(any " : ") string Pretty.ty) in
    vbox
    @@ iter_bindings ~sep:comma (fun f l -> List.iter ~f:(uncurry f) l) pp_pair

(** Find the type of a variable in gamma *)
let find : gamma -> string -> ty option = List.Assoc.find ~equal:String.equal

(** Add a (var, type) pair to gamma *)
let add : gamma -> string -> ty -> gamma = List.Assoc.add ~equal:String.equal

type cons = ty * ty [@@deriving equal, compare, show]
(** A constraint is a pair (t1,t2) that asserts t1 == t2 *)

(** Pretty-printer for cons *)
let pp_cons : cons Fmt.t =
    fun ppf (t1, t2) -> Fmt.pf ppf "%a == %a" Pretty.ty t1 Pretty.ty t2

(*******************************************
 *         Type Substitution (Sigma)       *
 *******************************************)

type soln = (string * ty) list [@@deriving equal, compare, show]
(** The solution to a list of type equations is 
   * a substitution from type variables to types *)

(** Pretty-printer for soln *)
let pp_soln : soln Fmt.t =
    let open Fmt in
    let pp_pair = hbox (pair ~sep:(any " |-> ") string Pretty.ty) in
    iter_bindings (fun f l -> List.iter ~f:(uncurry f) l) pp_pair

(*******************************************
 *         Type Inference Utils            *
 *******************************************)

module Utils = struct
    (** Substitute type variable [x] with type [t] in [ty] context [c] *)
    let rec subst (x : string) (t : ty) (c : ty) : ty = 
        match c with 
        | TVar y -> if String.equal x y then t else c 
        | TInt -> TInt
        | TBool -> TBool
        | TList elem_t -> TList (subst x t elem_t)
        | TFun (param_t, ret_t) -> TFun (subst x t param_t, subst x t ret_t) 
        | TProd (t1, t2) -> TProd (subst x t t1, subst x t t2) 
        | TSum (t1, t2) -> TSum (subst x t t1, subst x t t2)
        | TUnit -> TUnit
        | TVoid -> TVoid 

    (** Compute the free variable set of an [ty] *)
    let rec free_vars (t : ty) : Vars.t =
        match t with
        | TVar x -> Vars.singleton x
        | TInt | TBool -> Vars.empty
        | TList t' -> free_vars t'
        | TFun (t1, t2) | TProd (t1, t2) | TSum (t1, t2) ->
            Vars.union (free_vars t1) (free_vars t2)
        | TUnit | TVoid -> Vars.empty

    (** Apply a soln [s] to type [t] by performing all substitutions in [s] *)
    let apply_soln (s : soln) (t : ty) : ty =
        fold_left (fun acc (x, sub_t) -> subst x sub_t acc) t s

    let cata ~var : ty -> ty =
        let rec go = function
        | TVar x -> var x
        | (TInt | TBool | TUnit | TVoid) as t -> t
        | TList t -> TList (go t)
        | TFun (t1, t2) -> TFun (go t1, go t2)
        | TProd (t1, t2) -> TProd (go t1, go t2)
        | TSum (t1, t2) -> TSum (go t1, go t2)
        in
        go

    let subst_cs (x : string) (t : ty) (cs : cons list) : cons list =
        map (fun (t1, t2) -> (subst x t t1, subst x t t2)) cs

    let subst_multi (s : soln) : ty -> ty =
        cata ~var:(fun x ->
            match List.Assoc.find ~equal:String.equal s x with
            | Some t -> t
            | None -> raise (Type_error Fmt.(str "Unbound type variable %s" x)))

    (** Alpha-rename type variables (to 't0, 't1, 't2, ...) *)
    let normalize (t : ty) : ty =
        let s =
        t |> free_vars |> Vars.to_list
        |> List.mapi ~f:(fun i x -> (x, TVar ("'t" ^ Int.to_string (i + 1))))
        in
        subst_multi s t
end

(*******************************************
 *        Type Inference Engine            *  
 *******************************************)
module Infer = struct
    (** The list of accumulated constraints *)
    let _cs : cons list ref = ref []

    (** Add a constraint to the accumulator. Call it with [t1 === t2]. *)
    let ( === ) (t1 : ty) (t2 : ty) : unit =
        (* If you prefer the "printf" school of debugging, uncomment the following line,
        BUT DON'T FORGET TO REMOVE IT BEFORE YOU SUBMIT *)
        (* Fmt.epr "[constraint] %a\n%!" pp_cons (t1, t2); *)
        _cs := (t1, t2) :: !_cs

    (** Return the current list of constraints *)
    let curr_cons_list () : cons list = !_cs

    (******************************************
    *         Fresh Variable Helpers         *
    ******************************************)

    (** Counter to produce fresh variables *)
    let var_counter = ref 1

    (** Type string *)
    let ty_str_of_int (i : int) : string = "'X" ^ Int.to_string i

    (** Return the current var counter and increment it  *)
    let incr () =
        let v = !var_counter in
        var_counter := v + 1;
        v

    (** Generate a fresh string. For internal use only. *)
    let fresh_var_str () : string = ty_str_of_int (incr ())

    (** Generate a fresh [ty] type variable. Call it using [fresh_var ()]. *)
    let fresh_var () : ty = TVar (fresh_var_str ())

    (*******************************************
    *         Constraint Generation           *
    *******************************************)

    (** Abstractly evaluate an expression to a type.
    * This function also generates constraints and accumulates them into 
    * the list [cs] whenever you call [t1 === t2]. *)
    let rec abstract_eval (gamma : gamma) (e : expr) : ty =
        (* The following line loads functions in Ast.Ty module, allowing you to write
        [int] for [TInt], [bool] for [TBool], [t1 => t2] for [TFun(t1, t2)],
        [list t] for TList(t), and [t1 * t2] for [TProd(t1, t2)].
        However, you don't have to use the Ast.Ty functions, and you can just
        call the appropriate [ty] constructors. *)
        let open Ty in
        (* If you prefer the "printf" school of debugging, uncomment the following line,
        BUT DON'T FORGET TO COMMENT IT OUT BEFORE YOU SUBMIT *)
        (* Fmt.epr "[abstract_eval] %a\n%!" Ast.Pretty.expr e; *)
        (* Fmt.epr "[abstract_eval] Gamma:\n%!  %a\n%!" pp_gamma gamma; *)
        try 
            match e with Num _ -> TInt | True | False -> TBool 
            | Binop (_, lhs, rhs) -> 
                let lhs_ty = abstract_eval gamma lhs in
                let rhs_ty = abstract_eval gamma rhs in
                lhs_ty === TInt;
                rhs_ty === TInt;
                TInt
            | Var x -> 
                (match find gamma x with
                | Some t -> t
                | None -> ty_err ("Unbound variable " ^ x))
            | Lambda (param_t, (param, body)) ->
                let param_t' = 
                    (match param_t with
                    | Some t -> t 
                    | None -> fresh_var ())
                in
                let body_t = abstract_eval ((param, param_t')::gamma) body in 
                TFun (param_t', body_t)
            | App (fn, arg) ->
                let fn_t = abstract_eval gamma fn in
                let arg_t = abstract_eval gamma arg in
                let ret_t = fresh_var () in
                fn_t === TFun (arg_t, ret_t);
                ret_t 
            | Let (value, (name, body)) -> 
                let value_t = abstract_eval gamma value in
                abstract_eval ((name, value_t)::gamma) body
            | IfThenElse (cond, tt, ff) -> 
                let cond_t = abstract_eval gamma cond in
                let tt_t = abstract_eval gamma tt in
                let ff_t = abstract_eval gamma ff in 
                cond_t === TBool;
                tt_t === ff_t;
                tt_t
            | Comp (_, lhs, rhs) -> 
                let lhs_t = abstract_eval gamma lhs in
                let rhs_t = abstract_eval gamma rhs in
                lhs_t === TInt;
                rhs_t === TInt;
                TBool
            | ListNil elem_t ->
                let elem_t' = 
                    match elem_t with
                    | Some t -> t
                    | None -> fresh_var ()
                in
                TList elem_t'
            | ListCons (head, tail) -> 
                let head_t = abstract_eval gamma head in
                let tail_t = abstract_eval gamma tail in
                let elem_t = fresh_var () in
                tail_t === TList elem_t;
                head_t === elem_t;
                TList elem_t
            | ListMatch (scrut, nil_case, (h, (t, cons_case))) -> 
                let scrut_t = abstract_eval gamma scrut in
                let elem_t = fresh_var () in
                scrut_t === TList elem_t;
                let nil_t = abstract_eval gamma nil_case in 
                let cons_t = abstract_eval ((h, elem_t)::(t, TList elem_t)::gamma) cons_case in
                nil_t === cons_t;
                nil_t
            | Fix (expect_t, (self, body)) ->
                let expect_t' = match expect_t with
                | Some t -> t 
                | None -> fresh_var () 
                in
                let body_t = abstract_eval ((self, expect_t')::gamma) body in
                expect_t' === body_t;
                body_t
            | Annot (body, expect_t) -> 
                let body_t = abstract_eval gamma body in
                body_t === expect_t;
                expect_t
            | Unit -> TUnit
            | I1 e ->
                let t = abstract_eval gamma e in
                let t1 = fresh_var () in
                let t2 = fresh_var () in
                t === TProd (t1, t2);
                t1
            | I2 e -> 
                let t = abstract_eval gamma e in
                let t1 = fresh_var () in
                let t2 = fresh_var () in
                t === TProd (t1, t2);
                t2
            | Both (e1, e2) -> 
                let t1 = abstract_eval gamma e1 in
                let t2 = abstract_eval gamma e2 in
                TProd (t1, t2)
            (* void *)
            | Absurd e ->
                let t = abstract_eval gamma e in
                t === TVoid;
                t
            (* external choice *)
            | E1 e ->
                let t1 = abstract_eval gamma e in
                let t2 = fresh_var () in
                TSum (t1, t2)
            | E2 e ->
                let t1 = abstract_eval gamma e in
                let t2 = fresh_var () in
                TSum (t2, t1)
            | Either (e, (x, e1), (y, e2)) -> 
                let sum_t = abstract_eval gamma e in
                let t1 = fresh_var () in
                let t2 = fresh_var () in
                sum_t === TSum(t1, t2);
                let r1 = abstract_eval ((x, t1)::gamma) e1 in
                let r2 = abstract_eval ((y, t2)::gamma) e2 in
                r1 === r2;
                r1
        with Type_error msg ->
            ty_err (msg ^ Fmt.(str "\nin expression %a" Pretty.expr e))

    (*******************************************
    *           Constraint Solving            *
    *******************************************)

    (** unification algorithm *)
    and unify (cs : cons list) : soln =
    match cs with
    | [] -> []
    | (s, t)::cs' ->
        (* extract the first constraint as [c], and the remaining as [cs'] *)
        (match s, t with
        | s, t when equal_ty s t -> unify cs' 
        | TVar x, t when not (Vars.mem x (Utils.free_vars t)) -> 
            let cs'' = Utils.subst_cs x t cs' in
            let soln = unify cs'' in
            let t' = Utils.apply_soln soln t in
            (x, t')::soln
        | t, TVar x -> unify ((TVar x, t)::cs')
        | TList elem_t1, TList elem_t2 ->
            unify ((elem_t1, elem_t2)::cs')
        | TFun (param_t1, ret_t1), TFun (param_t2, ret_t2) ->
            unify ((param_t1, param_t2)::(ret_t1, ret_t2)::cs')
        | TProd (a1, b1), TProd (a2, b2) ->
            unify ((a1, a2)::(b1, b2) :: cs')
        | TSum (a1, b1), TSum (a2, b2) ->
            unify ((a1, a2)::(b1, b2) :: cs')
        | _, _ -> ty_err "unification failed")
end

(*******************************************
 *             Type inference              *
 *******************************************)

(** Infer the type of expression [e] in the environment [g] *)
let infer_with_gamma ~(gamma : gamma) (e : expr) : ty =
    let t = Infer.abstract_eval gamma e in
    let s = Infer.unify (Infer.curr_cons_list ()) in
    Utils.apply_soln s t |> Utils.normalize

(** Infer the type of expression [e] *)
let infer (e : expr) : ty = infer_with_gamma ~gamma:[] e
