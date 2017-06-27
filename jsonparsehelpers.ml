open Utility
open Value
open Types


type 't parse_match = 
   [ `Keys of (string list * (string list -> 't))
   | `String of string -> 't
   | `Float of float -> 't
   | `Int of int -> 't
   | `Bool of bool -> 't
   | `Char of char -> 't
   ]

let parse_match_action_str_list = 
   function
   | `Keys (_, action) -> action
   | _ -> failwith "Unexpected parse_match_action"

let parse_match_action_str =
   function
   | `String action -> action
   | _ -> failwith "Unexpected parse_match_action"

let parse_match_action_fl =
   function
   | `Float action -> action
   | _ -> failwith "Unexpected parse_match_action"

let parse_match_action_i =
   function
   | `Int action -> action
   | _ -> failwith "Unexpected parse_match_action"

let parse_match_action_b =
   function
   | `Bool action -> action
   | _ -> failwith "Unexpected parse_match_action"

let parse_match_action_c =
   function
   | `Char action -> action
   | _ -> failwith "Unexpected parse_match_action"


let parse_json_record actions (r : Value.t) = 
   let follow actions r = 
      let keys = List.map (fun (k,_) -> k) r in
      let action = List.find (fun action -> 
         match action with
         | `Keys (v,_) -> v = keys
         | _ -> false ) actions in
      (parse_match_action_str_list action) (List.map (fun (_,v) -> v) r)
      in
   match r with 
   | `Record vals ->
         follow actions vals
   | `String str -> 
         let action = List.find (fun action -> 
         match action with 
         | `String fn -> true
         | _ -> false
         ) actions in
         (parse_match_action_str action) str
   | `Float fl -> 
         let action = List.find (fun action -> 
         match action with 
         | `Float fn -> true
         | _ -> false
         ) actions in
         (parse_match_action_fl action) fl
   | `Int i -> 
         let action = List.find (fun action -> 
         match action with 
         | `Int i -> true
         | _ -> false
         ) actions in
         (parse_match_action_i action) i
   | `Bool b ->
         let action = List.find (fun action -> 
         match action with 
         | `Bool b -> true
         | _ -> false
         ) actions in
         (parse_match_action_b action) b
   | `Char c ->
         let action = List.find (fun action ->
            match action with
            | `Char c -> true
            | _ -> false
         ) actions in 
         (parse_match_action_c action) c
   | _ -> failwith "Didn't find matching record"



let rec parse_json_phrase r : Types.lens_phrase =
   parse_json_record [
      `String (fun s -> `Constant (`String s));
      `Int (fun i -> `Constant (`Int i));
      `Float (fun f -> `Constant (`Float f));
      `Char (fun c -> `Constant (`Char c));
      `Keys (["var"], fun [var] -> `Var (unbox_string var));
      `Keys (["infx"; "l"; "r"], fun [op; l; r] -> 
         `InfixAppl (Operators.binop_of_string (unbox_string op), parse_json_phrase l, parse_json_phrase r));
   ] r

let parse_json_col (r : Value.t) =
   parse_json_record [`Keys (["table"; "name"; "alias"; "typ"; "present"], fun [table; name; alias; typ; present] -> {
      table = unbox_string table;
      name = unbox_string name;
      alias = unbox_string alias;
      typ = DesugarDatatypes.read ~aliases:Env.String.empty (unbox_string typ);
      present = unbox_bool present
   })] r

let parse_json_cols cols =
   let cols = unbox_list cols in
   let cols = List.map parse_json_col cols in
   cols

let parse_json_fds l = 
   let fn strs = List.map unbox_string (unbox_list strs) in
   let l = unbox_list l in
   let l = List.map (fun l -> let [r; s] = unbox_list l in fn r, fn s) l in
   FunDepSet.of_lists l

let parse_json_sort r : lens_sort =
   parse_json_record [
      `Keys (["fds"; "phrase"; "cols"], fun [fds; phrase; cols] -> (parse_json_fds fds, Some (parse_json_phrase phrase), parse_json_cols cols));
      `Keys (["fds"; "cols"], fun [fds; phrase; cols] -> (parse_json_fds fds, None, parse_json_cols cols))
   ] r


