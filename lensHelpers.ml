open Types
open Utility
open Value

(* Helper methods *)
let try_find p l = try Some (List.find p l) with Not_found -> None | NotFound _ -> None

let get_record_val (key : string) (r : Value.t) = 
    let columns = match r with `Record c -> c in
    let (_, value) = List.find (fun (name, value) -> name = key) columns in
    value

    (* this function assumes the two records have identical signatures, not considering order *)
let records_equal recA recB =
    not (List.exists (fun (name, value) -> get_record_val name recB <> value) (unbox_record recA))

    (* Drop related methods *)
let remove_record_type (a : string) (r : typ) =
    match r with `Record (fields, row_var, dual) -> 
        let (entry, fields) = StringMap.pop a fields in
        `Record (fields, row_var, dual)

let drop_record_row (a : string) (record : Value.t) =
    let columns = List.filter (fun (name, value) -> name <> a) (unbox_record record) in
    box_record columns


let restore_column (drop : string) (key : string) (default : Value.t) (row : Value.t) (records : Value.t) =
    let unb_records = unbox_list records in
    let record = try_find (fun x -> records_equal (drop_record_row drop x)  row) unb_records in
    match record with
    | Some r -> r
    | None -> 
        let keyVal = get_record_val key row in 
        let record = try_find (fun x -> get_record_val key x = keyVal) unb_records in
        let dropVal = match record with
        | Some r -> get_record_val drop r
        | None -> default in
        box_record ((drop, dropVal) :: unbox_record row) 

(* get / put operations *)

let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens
    | _ -> failwith (string_of_value lens)

let rec lens_get (lens : Value.t) =
    match lens with
    | `Lens _ -> failwith "Non memory lenses not implemented."
    | `LensMem (table, rtype) -> table
    | `LensDrop (lens, drop, key, def, rtype) ->
        let records = lens_get lens in
        let result = List.map (fun a -> drop_record_row drop a) (unbox_list records) in
          `List result

let rec lens_put_mem (lens : Value.t) (data : Value.t) =
    match lens with
    | `Lens _ -> data
    | `LensMem _ -> data
    | `LensDrop (l, drop, key, def, rtype) -> 
            let records = lens_get l in
            let newRecords = List.map (fun x -> restore_column drop key def x records) (unbox_list data) in
                box_list newRecords

let rec lens_put (lens : Value.t) (data : Value.t) =
    if is_memory_lens lens then
        lens_put_mem lens data
    else
        data

