open Ast

let todo () = failwith "TODO"

exception Stuck of string
(** Exception indicating that evaluation is stuck *)

(** Raises an exception indicating that evaluation got stuck. *)
let im_stuck msg = raise (Stuck msg)

let rec free_vars (e : expr) : Vars.t =
    (* This line imports the functions in Vars, so you can write [diff .. ..]
       instead of [Vars.diff .. ..] *)
    let open Vars in
    (* Your code goes here *)
    match e with
    | Num _ -> empty
    | Binop (_, lhs, rhs) -> union (free_vars lhs) (free_vars rhs)
    | Var x -> singleton x
    | Lambda (_, (param, body)) -> diff (free_vars body) (singleton param)
    | App (fn, arg) -> union (free_vars fn) (free_vars arg)
    | Let (value, (name, expr)) -> union (free_vars value) (diff (free_vars expr) (singleton name))
    | True -> empty
    | False -> empty 
    | IfThenElse (cond, tt, ff) -> union (union (free_vars cond) (free_vars tt)) (free_vars ff) 
    | Comp (_, lhs, rhs) -> union (free_vars lhs) (free_vars rhs)  
    | ListNil _ -> empty 
    | ListCons (head, tail) -> union (free_vars head) (free_vars tail) 
    | ListMatch (scrutinee, nil_case, (h, (t, cons_case))) ->
        let scrutinee_vars = free_vars scrutinee in
        let nil_vars = free_vars nil_case in
        let cons_vars = diff (diff (free_vars cons_case) (singleton h)) (singleton t) in 
        union (union scrutinee_vars nil_vars) cons_vars 
    | Fix (_, (self, body)) -> diff (free_vars body) (singleton self) 
    | _ -> im_stuck (Fmt.str "Unknown expression type: %a" Pretty.expr e)

(** Perform substitution c[x -> e], i.e., substituting x with e in c *)
let rec subst (x : string) (e : expr) (c : expr) : expr =
    match c with
    | Num n -> Num n
    | Binop (binop, lhs, rhs) -> Binop (binop, subst x e lhs, subst x e rhs)
    | Var y -> if x = y then e else Var y
    | Lambda (param_t, (param, body)) ->
        let body' = 
            if String.equal x param || Vars.mem param (free_vars e)
            then body 
            else subst x e body in
        Lambda (param_t, (param, body'))
    | App (fn, arg) -> App (subst x e fn, subst x e arg)
    | Let (value, (name, body)) ->
        let body' = 
            if String.equal x name || Vars.mem name (free_vars e) 
            then body 
            else subst x e body in 
        Let (subst x e value, (name, body'))
    | True -> True 
    | False -> False 
    | IfThenElse (cond, tt, ff) -> IfThenElse (subst x e cond, subst x e tt, subst x e ff) 
    | Comp (relop, lhs, rhs) -> Comp (relop, subst x e lhs, subst x e rhs) 
    | ListNil elem_t -> ListNil elem_t 
    | ListCons (head, tail) -> ListCons (subst x e head, subst x e tail) 
    | ListMatch (scrutinee, nil_case, (h, (t, cons_case))) -> 
        let scrutinee' = subst x e scrutinee in
        let nil_case' = subst x e nil_case in
        let cons_case' = 
            if String.equal x h || String.equal x t
            then cons_case 
            else subst x e cons_case 
        in
        ListMatch (scrutinee', nil_case', (h, (t, cons_case')))
    | Fix (expected_t, (self, body)) ->
        let body' =
            if String.equal x self 
            then body 
            else subst x e body 
        in 
        Fix (expected_t, (self, body'))    
    | _ -> im_stuck (Fmt.str "Unknown expression type: %a" Pretty.expr e)

(** Evaluate expression e *)
let rec eval (e : expr) : expr =
    try 
        match e with   
        | Num n -> Num n
        | Binop (binop, lhs, rhs) -> 
            (match eval lhs, eval rhs with
            | Num x, Num y -> 
                (match binop with
                | Add -> Num (x + y)
                | Sub -> Num (x - y)
                | Mul -> Num (x * y))
            | _, _ -> im_stuck (Fmt.str "Invalid binop: %a" Pretty.expr e))
        | Var _ -> im_stuck (Fmt.str "Unassigned: %a" Pretty.expr e) 
        | Lambda (param_t, binder)-> Lambda (param_t, binder)
        | App (fn, arg) -> 
            (match eval fn with
            | Lambda (_, (param, body)) -> eval (subst param (eval arg) body) 
            | _ -> im_stuck (Fmt.str "Application to non lambda: %a" Pretty.expr e))
        | Let (value, (name, body)) -> eval (subst name (eval value) body)
        | True -> True 
        | False -> False 
        | IfThenElse (cond, tt, ff) -> 
            (match eval cond with
            | True -> eval tt
            | False -> eval ff
            | _ -> im_stuck (Fmt.str "Non-bool in if statement: %a" Pretty.expr e))
        | Comp (relop, lhs, rhs) -> 
            (match eval lhs, eval rhs with
            | Num x, Num y -> 
                (match relop with
                | Eq -> if x = y then True else False 
                | Gt -> if x > y then True else False
                | Lt -> if x < y then True else False)
            | _, _ -> im_stuck (Fmt.str "Non-number operands to comparison: %a" Pretty.expr e))      
        | ListNil elem_t -> ListNil elem_t
        | ListCons (head, tail) -> ListCons (eval head, eval tail)
        | ListMatch (scrutinee, nil_case, (h, (t, cons_case))) -> 
            (match eval scrutinee with
            | ListNil _ -> eval nil_case
            | ListCons (head, tail) -> eval (subst h head (subst t tail cons_case))
            | _ -> im_stuck (Fmt.str "List error: %a" Pretty.expr e))
        | Fix (expected_t, (self, body)) -> eval (subst self (Fix (expected_t, (self, body))) body)
        (* Some | None ? *)
        | E1 e1 -> E1 (eval e1) 
        | E2 e2 -> E2 (eval e2) 
        | Either (e', (x, e1), (y, e2)) ->
            (match eval e' with
            | E1 e1' -> eval (subst x e1' e1)  
            | E2 e2' -> eval (subst y e2' e2)
            | _ -> im_stuck (Fmt.str "Either on non-choice: %a" Pretty.expr e))
        | I1 e1 -> todo ()
        | I2 e2 -> todo ()
        | Both (e1, e2) -> todo ()
        | Unit -> Unit
        | Absurd e -> (match eval e with _ -> im_stuck (Fmt.str "Void cannot have a value: %a" Pretty.expr e)) 
        | _ -> im_stuck (Fmt.str "Ill-formed expression: %a" Pretty.expr e)
    with Stuck msg ->
        im_stuck (Fmt.str "%s\nin expression %a" msg Pretty.expr e)
