open Ast
open Base

type env = (string * ty) list
(** Typing environment, aka Gamma *)

(** Helper function to look up a variable in the env *)
let find : env -> string -> ty option = List.Assoc.find ~equal:String.equal

(** Helper function to insert a (variable, ty) pair into the env *)
let add : env -> string -> ty -> env = List.Assoc.add ~equal:String.equal

exception Type_error of string

let ty_err msg = raise (Type_error msg)

let rec equal_ty (t1 : ty) (t2 : ty) : bool =
    match t1, t2 with
    | TVar x, TVar y -> String.equal x y 
    | TInt, TInt -> true
    | TBool, TBool -> true
    | TList elem_t1, TList elem_t2 -> equal_ty elem_t1 elem_t2 
    | TFun (param_t1, ret_t1), TFun (param_t2, ret_t2) -> 
        equal_ty param_t1 param_t2 && equal_ty ret_t1 ret_t2  
    | TUnit, TUnit -> true 
    | TVoid, TVoid -> true
    | TProd (a1, b1), TProd (a2, b2) ->
        equal_ty a1 a2 && equal_ty b1 b2
    | TSum (a1, b1), TSum (a2, b2) ->
        equal_ty a1 a2 && equal_ty b1 b2
    | _ -> false

let rec abstract_eval (env : env) (e : expr) : ty =
    try
        match e with
        (* T-Int rule *)
        | Num _ -> TInt
        (* T-True and T-false *)
        | True | False -> TBool
        (* Your code here *)
        | Binop (_, lhs, rhs) -> 
            let lhs_ty = abstract_eval env lhs in
            let rhs_ty = abstract_eval env rhs in
            if equal_ty lhs_ty TInt && equal_ty rhs_ty TInt
            then TInt
            else ty_err "Arith expects int operands"
        | Var x -> 
            (match find env x with
            | Some t -> t
            | None -> ty_err ("Unbound variable " ^ x))
        | Lambda (param_t, (param, body)) ->
            (match param_t with
            | Some param_t' ->
                let env' = add env param param_t' in
                let body_t = abstract_eval env' body in
                TFun (param_t', body_t)
            | None -> ty_err "Lambda requires type annotation")
        | App (fn, arg) ->
            let fn_t = abstract_eval env fn in
            let arg_t = abstract_eval env arg in
            (match fn_t with
            | TFun (param_t, ret_t) ->
                if equal_ty arg_t param_t
                then ret_t
                else ty_err "Function argument type mismatch"
            | _ -> ty_err "Application of non-function")
        | Let (value, (name, body)) -> 
            let value_t = abstract_eval env value in
            let env' = add env name value_t in
            abstract_eval env' body
        | IfThenElse (cond, tt, ff) -> 
            let cond_ty = abstract_eval env cond in
            if not (equal_ty cond_ty TBool) then ty_err "Condition must be bool type" else
            let tt_t = abstract_eval env tt in
            let ff_t = abstract_eval env ff in 
            if equal_ty tt_t ff_t
            then tt_t
            else ty_err "Branches must have same type"
        | Comp (_, lhs, rhs) -> 
            let lhs_t = abstract_eval env lhs in
            let rhs_t = abstract_eval env rhs in
            if equal_ty lhs_t TInt && equal_ty rhs_t TInt 
            then TBool
            else ty_err "Comp expects int operands"
        | ListNil elem_t ->
            (match elem_t with
            | Some elem_t' -> TList elem_t'
            | None -> ty_err "ListNil requires type annotation")
        | ListCons (head, tail) -> 
            let head_t = abstract_eval env head in
            let tail_t = abstract_eval env tail in
            (match tail_t with
            | TList elem_t ->
                if equal_ty head_t elem_t
                then TList elem_t
                else ty_err "Head type mismatch in list"
            | _ -> ty_err "Tail must be list")
        | ListMatch (scrutinee, nil_case, (h, (t, cons_case))) -> 
            (match abstract_eval env scrutinee with
            | TList elem_t ->
                let nil_t = abstract_eval env nil_case in
                let env' = add env h elem_t in
                let env'' = add env' t (TList elem_t) in
                let cons_ty = abstract_eval env'' cons_case in
                if equal_ty nil_t cons_ty
                then nil_t
                else ty_err "ListMatch branches must have same type"
            | _ -> ty_err "ListMatch expects a list")
        | Fix (expected_t, (self, body)) ->
            (match expected_t with
            | Some expected_t' -> 
                let env' = add env self expected_t' in
                let body_t = abstract_eval env' body in
                if equal_ty body_t expected_t'
                then expected_t'
                else ty_err "Fix body does not match annotation"
            | None -> ty_err "Fix requires type annotation")
        | Annot (body, expected_t) -> 
            let expected_t' = abstract_eval env body in
            if equal_ty expected_t expected_t'
            then expected_t
            else ty_err "Type annotation does not match actual type"
        | Unit -> TUnit
        | Both (e1, e2) -> 
            let t1 = abstract_eval env e1 in
            let t2 = abstract_eval env e2 in
            TProd (t1, t2)
        | I1 e1 ->
            (match abstract_eval env e1 with
            | TProd (t1, _) -> t1 
            | _ -> ty_err  "Expected prod type")
        | I2 e2 -> 
            (match abstract_eval env e2 with
            | TProd (_, t2) -> t2 
            | _ -> ty_err  "Expected prod type")
        (* void *)
        | Absurd _ -> TVoid
        (* external choice *)
        | E1 e1 -> failwith "TODO"
        | E2 e2 -> failwith "TODO" 
        | Either (e, b1, b2) -> failwith "TODO" 
    with Type_error msg -> ty_err (msg ^ "\nin expression " ^ show_expr e)

let rec size (t : ty) : int option =
    match t with 
    | TVar _ -> None 
    | TInt -> None
    | TBool -> Some 2
    | TList elem_t ->
        (match size elem_t with
        | Some 0 -> Some 1
        | _ -> None)
    | TFun (param_t, ret_t) -> 
        (match size param_t, size ret_t with
        | Some s1, Some s2 -> 
            let rec pow a = function
            | 0 -> 1
            | 1 -> a
            | n -> 
                let b = pow a (n / 2) in
                b * b * (if n % 2 = 0 then 1 else a)
            in
            Some (pow s2 s1)
        | _ -> None)
    | TProd (t1, t2) -> 
        (match size t1, size t2 with
        | Some 0, _ | _, Some 0 -> Some 0
        | Some s1, Some s2 -> Some (s1 * s2)
        | _ -> None)
    | TSum (t1, t2) -> 
        (match size t1, size t2 with
        | Some s1, Some s2 -> Some (s1 + s2)
        | _ -> None)
    | TUnit -> Some 1 
    | TVoid -> Some 0 
