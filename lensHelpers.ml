open Types
open Utility

let remove_record_type (a : string) (r : typ) =
    match r with `Record (fields, row_var, dual) -> 
        let (entry, fields) = StringMap.pop a fields in
        `Record (fields, row_var, dual)


let lens_get (lens : Value.t) =
    match lens with
    | `Lens _ -> failwith "Non memory lenses not implemented."
    | `LensMem (table, rtype) -> table


