open Types
open Sugartypes
open Utility
open Value
open LensRecordHelpers


let value_of_constant : Constant.constant -> Value.t  = function
    | `Int a -> `Int a
    | `Float f -> `Float f
    | `String s -> `String s
    | `Bool b -> `Bool b
    | _ -> failwith "Unsupported constant type."

let constant_of_value : Value.t -> Constant.constant  = function
    | `Int a -> `Int a
    | `Float f -> `Float f
    | `String s -> `String s
    | `Bool b -> `Bool b
    | _ -> failwith "Unsupported value type."

let translate_op_to_sql = function
    | "==" -> "="
    | "&&" -> "AND"
    | "||" -> "OR"
    | a -> a

let name_of_var (expr: phrase) =
    let expr,_ = expr in
    match expr with
    | `Var n -> n
    | _ -> failwith "Expected var."


let rec calculate_predicate (expr : phrase) (get_val : string -> Value.t) = 
    let expr, pos = expr in
    match expr with
    | `Constant c -> value_of_constant c
    | `Var v -> 
        begin
            try
                get_val v
            with NotFound _ -> failwith ("Could not find column " ^ v ^ ".")
        end
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
            | _ -> failwith "Unknown binary operation."
        end
    | `TupleLit l -> calculate_predicate (List.hd l) get_val
    | `FnAppl (fn, arg) ->
        begin
            match name_of_var fn with
            | "not" -> 
                let res = calculate_predicate (List.hd arg) get_val in
                let res = not (unbox_bool res) in
                box_bool res 
            | _ -> failwith "Unknown function."
        end
    | _ -> failwith "Unknown phrasenode for calculate_predicate."

let rec construct_query (expr : phrase) =
    let expr, pos = expr in
    match expr with
    | `Constant c -> Constant.string_of_constant c
    | `Var v -> "`" ^ v ^ "`"
    | `InfixAppl ((_, op), a1, a2) -> construct_query a1 ^ " " ^ translate_op_to_sql (string_of_binop op) ^ " " ^ construct_query a2
    | `TupleLit l -> "(" ^ List.fold_left (fun a b -> a ^ ", " ^ (construct_query b)) (construct_query (List.hd l)) (List.tl l)  ^ ")"
    | `UnaryAppl ((_, op), a1) ->  string_of_unary_op op ^ construct_query a1
    | `FnAppl (fn, arg) -> String.uppercase_ascii (name_of_var fn) ^ " (" ^ construct_query (List.hd arg) ^ ")"
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
    | `FnAppl (fn, args) -> `FnAppl(fn, List.map (fun x -> replace_var x repl) args),pos
    | _ -> failwith "Unknown operation"

let create_phrase_and (left : phrase) (right : phrase) =
    `InfixAppl (([], `And), left, right), Sugartypes.dummy_position

let create_phrase_equal (left : phrase) (right : phrase) =
    `InfixAppl (([], `Name "=="), left, right), Sugartypes.dummy_position

let create_phrase_var (name : string) =
    `Var name, Sugartypes.dummy_position

let create_phrase_constant_of_record_col (r : Value.t) (key : string) =
    `Constant (constant_of_value (get_record_val key r)), Sugartypes.dummy_position

let create_phrase_not (arg : phrase) = 
    `FnAppl (create_phrase_var "not", [arg]), Sugartypes.dummy_position

(*let calculate_predicate (expr : phrase) pred = 
    (* let _ = Debug.print (construct_query expr) in
    let _ = Debug.print (string_of_value (calculate_predicate expr (fun a -> match a with "itemID" -> `Int 6 | "name" -> `String "john"))) in 
    let _ = Debug.print (construct_query (replace_var expr ["itemID", `Int 5;"test", `Int 3])) in
    let expr, pos = expr in
    let expr2 = (expr,pos) in
    let applied = replace_var expr2 ["itemID", `Int 5] in
    let testExpr =  `InfixAppl (([], `And), (`TupleLit [expr2],pos), (`TupleLit [applied],pos)),pos in
    let _ = Debug.print (construct_query testExpr) in *)
    `Bool true *)

let calculate_predicate_rec (expr : phrase) (r : Value.t) = 
    let get_val = fun x -> get_record_val x r in
    calculate_predicate expr get_val
