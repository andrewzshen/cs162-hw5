open Base
open Ast

let todo () = failwith "TODO"

(** These types can be interpreted as propositions *)
let types : (string * ty) list =
    List.map
        ~f:(fun (p, s) -> (p, Parser.Ty.parse_string s))
        [
            ("always_true", "()");
            ("always_false", "!");
            ("everything", "'p");
            ("everything_implies_truth", "'p -> ()");
            ("falsehood_implies_everything", "! -> 'q");
            ("everything_implies_itself", "'p -> 'p");
            ("modus_ponens", "'p * ('p -> 'q) -> 'q");
            ("both_true_implies_left_true", "'p * 'q -> 'p");
            ("either_true_implies_left_true", "'p + 'q -> 'p");
            ("conjunction_is_commutative", "'p * 'q -> 'q * 'p");
            ("disjunction_is_commutative", "'p + 'q -> 'q + 'p");
            ( "conjunction_distributes_over_disjunction",
                "'p * ('q + 'r) -> ('p * 'q) + ('p * 'r)" );
            ( "disjunction_distributes_over_conjunction",
                "'p + ('q * 'r) -> ('p + 'q) * ('p + 'r)" );
            ("curry", "('p * 'q -> 'r) -> ('p -> ('q -> 'r))");
            ("uncurry", "('p -> ('q -> 'r)) -> ('p * 'q -> 'r)");
        ]

(** For each proposition, determine whether it is valid (i.e. the truth table is always T) *)
let is_valid () : (string * bool) list =
    [
        ("always_true", true);
        ("everything", false);
        ("everything_implies_truth", true);
        ("falsehood_implies_everything", true);
        ("everything_implies_itself", true);
        ("modus_ponens", true);
        ("both_true_implies_left_true", true);
        ("either_true_implies_left_true", false);
        ("conjunction_is_commutative", true);
        ("disjunction_is_commutative", true);
        ("conjunction_distributes_over_disjunction", true);
        ("disjunction_distributes_over_conjunction", true);
        ("curry", true);
        ("uncurry", true);
    ]

(** For each type, give a lambda-plus expression that can be inferred to have said type.
  If there're no such expressions, simply put a [None]. Otherwise, put [Some <str>] where
  <str> is the expression in concrete syntax. *)
let expressions () : (string * expr option) list =
    List.map
        ~f:(fun (p, s) -> (p, Option.map ~f:Parser.Expr.parse_string s))
        [
            ("always_true", Some "()");
            ("everything", None);
            ("everything_implies_truth", Some "lambda x. ()");
            ("falsehood_implies_everything", Some "lambda x. match x with end");
            ("everything_implies_itself", Some "lambda x. x");
            ("modus_ponens", Some "lambda x. (snd x) (fst x)");
            ("both_true_implies_left_true", Some "lambda x. fst x");
            ("either_true_implies_left_true", None);
            ("conjunction_is_commutative", Some "");
            ("disjunction_is_commutative", Some "");
            ("conjunction_distributes_over_disjunction", Some "");
            ("disjunction_distributes_over_conjunction", Some "");
            ("curry", Some "");
            ("uncurry", Some "");
        ]

let synthesize (t : ty) : expr option = todo ()
