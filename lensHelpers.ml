open Types
open Utility

let remove_record_type (a : string) (r : typ) =
    match r with `Record (fields, row_var, dual) -> 
        let (entry, fields) = StringMap.pop a fields in
        `Record (fields, row_var, dual)

let drop_record_row (a : string) (r : Value.t) =
    let columns = match r with `Record c -> c in
    let columns = List.filter (fun (name, value) -> name <> a) columns in
      `Record columns


let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens

let rec lens_get (lens : Value.t) =
    match lens with
    | `Lens _ -> failwith "Non memory lenses not implemented."
    | `LensMem (table, rtype) -> table
    | `LensDrop (lens, drop, key, def, rtype) ->
        let records = match lens_get lens with `List a -> a in
        let result = List.map (fun a -> drop_record_row drop a) records in
          `List result


