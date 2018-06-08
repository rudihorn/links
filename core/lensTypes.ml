open Types
open Utility
open Value

let unpack_field_spec (typ : Types.field_spec) = 
    match typ with
    | `Present t -> t
    | _ -> failwith "Expected `Present"

let extract_record_type (t : Types.typ) =
    match t with
    | `Record _ as r -> r
    | `Application (_, [`Type (`Record _ as r)]) -> r
    | `Table (r, _, _) -> r
    | e -> failwith ("LensTypes does not type.") (* TODO: display incorrectly expected type **)

(** Returns the columns of a `Record type. **)
let record_fields (rt : Types.typ) = 
    match rt with 
    | `Record (fields, row_var, dual) -> fields 
    | e -> failwith "Expected a record type." (* TODO: display incorrectly expected type **)

let sort_cols_of_record (tableName : string) (typ : Types.typ) = 
    let fields = record_fields typ in
    let cols = StringMap.to_list (fun k v -> {table = tableName; name = k; alias = k; typ = unpack_field_spec v; present = true;}) fields in
    cols

let cols_of_record (typ: Types.typ) =
    let fields = record_fields typ in
    StringMap.to_list (fun k v -> k) fields

(** Generate a sort for a table with the given type **)
let sort_cols_of_table (tableName : string) (t : Types.typ) = 
    let rt = extract_record_type t in
    sort_cols_of_record tableName rt

let var_name (var, _pos : Sugartypes.phrase) = 
    match var with
    | `Var name -> name
    | _ -> failwith "Expected a `Var type"

let columns_of_phrase (key, _pos : Sugartypes.phrase) : string list = 
    match key with
    | `TupleLit keys -> List.map var_name keys
    | `Var name -> [name]
    | _ -> failwith "Expected a tuple or a variable."

