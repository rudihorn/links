open Types
open Sugartypes
open Utility
open Value


let value_of_constant : Constant.constant -> Value.t  = function
    | `Int a -> `Int a
    | `Float f -> `Float f
    | `String s -> `String s
    | `Bool b -> `Bool b

let constant_of_value : Value.t -> Constant.constant  = function
    | `Int a -> `Int a
    | `Float f -> `Float f
    | `String s -> `String s
    | `Bool b -> `Bool b

let translate_op_to_sql = function
    | "==" -> "="
    | "&&" -> "AND"
    | "||" -> "OR"
    | a -> a

let rec calculate_predicate (expr : phrase) (get_val) = 
    let expr, pos = expr in
    match expr with
    | `Constant c -> value_of_constant c
    | `Var v -> get_val v
    | `InfixAppl ((_, op), a1, a2) -> 
        let a1 = calculate_predicate a1 get_val in
        let a2 = calculate_predicate a2 get_val in
        begin
            match (string_of_binop op) with
            | "==" -> box_bool ( match a1 with `Bool b -> b == unbox_bool a2 | `Int i -> i == unbox_int a2 | `String s -> s = unbox_string a2)
            | "&&" -> box_bool (unbox_bool a1 && unbox_bool a2)
            | "+" -> box_int ((unbox_int a1) + (unbox_int a2))
            | "*" -> box_int (unbox_int a1 * unbox_int a2)
            | "-" -> box_int (unbox_int a1 - unbox_int a2)
        end
    | `TupleLit l -> calculate_predicate (List.hd l) get_val

let rec construct_query (expr : phrase) =
    let expr, pos = expr in
    match expr with
    | `Constant c -> Constant.string_of_constant c
    | `Var v -> "`" ^ v ^ "`"
    | `InfixAppl ((_, op), a1, a2) -> construct_query a1 ^ " " ^ translate_op_to_sql (string_of_binop op) ^ " " ^ construct_query a2
    | `TupleLit l -> "(" ^ List.fold_left (fun a b -> a ^ ", " ^ (construct_query b)) (construct_query (List.hd l)) (List.tl l)  ^ ")"
    | _ -> failwith "durr"

let rec replace_var (expr : phrase) (repl : (string * Value.t) list)  :  phrase=
    let expr, pos = expr in
    match expr with
    | `Constant _ -> expr, pos
    | `Var n -> 
        begin try 
            let _,v = List.find (fun (k,v) -> k = n) repl in
            `Constant (constant_of_value v),pos
            with NotFound _ -> expr,pos
        end
    | `UnaryAppl (a, arg) ->  `UnaryAppl(a, replace_var arg repl),pos
    | `InfixAppl (a, a1, a2) -> `InfixAppl (a, replace_var a1 repl, replace_var a2 repl),pos
    | `TupleLit (x :: []) -> `TupleLit (replace_var x repl :: []),pos
    | _ -> failwith "Unknown operation"

let calculate_predicate (expr : phrase) pred = 
    let _ = Debug.print (construct_query expr) in
    let _ = Debug.print (string_of_value (calculate_predicate expr (fun a -> match a with "itemID" -> `Int 6 | "name" -> `String "john"))) in 
    let _ = Debug.print (construct_query (replace_var expr ["itemID", `Int 5;"test", `Int 3])) in
    let expr, pos = expr in
    let expr2 = (expr,pos) in
    let applied = replace_var expr2 ["itemID", `Int 5] in
    let testExpr =  `InfixAppl (([], `And), (`TupleLit [expr2],pos), (`TupleLit [applied],pos)),pos in
    let _ = Debug.print (construct_query testExpr) in
    match expr  with 
    | `UnaryAppl _ -> failwith "unary"
    | `FnAppl _ -> failwith "fnappl"
    | `InfixAppl _ -> failwith "infix"
    | _ -> failwith "durr"
