open Types
open Utility
open Value
open LensFDHelpers


let get_lens_sort_fn_deps (fn_dep, _, _ : Types.lens_sort) : Types.fn_dep list =
    fn_dep

let get_lens_sort_cols (_, _, rowType : Types.lens_sort) = 
  rowType

let get_lens_sort_row_type (_, _, rowType : Types.lens_sort) = 
  let map : field_spec_map = List.fold_left (fun a (table, col, alias, typ) -> StringMap.add alias (`Present typ) a) StringMap.empty rowType in
  `Record (map, Unionfind.fresh `Closed, false)

let set_lens_sort_table_name (fn_dep, pred, rowType : Types.lens_sort) (table : string) =
    let rowType = List.map (fun (_, name, alias, typ) -> (table, name, alias, typ)) rowType in
    (fn_dep, pred, rowType)

let get_lens_col_by_alias (cols : lens_col list) alias =
    try 
        Some (List.find (fun (_,_,alias2,_) -> alias2 = alias) cols) 
    with 
        Not_found _ -> None

let get_lens_sort_col_by_alias sort alias = 
    let cols = get_lens_sort_cols sort in
    get_lens_col_by_alias cols alias

let get_lens_col_type (_, _, _, typ : Types.lens_col) = typ

let get_lens_col_alias (_, _, alias, _ : Types.lens_col) = alias

let set_lens_col_alias (table, name, _, typ : Types.lens_col) (new_alias : string) = (table, name, new_alias, typ)

let match_lens_col_alias (c1 : lens_col) (c2 : lens_col) = get_lens_col_alias c1 = get_lens_col_alias c2

let get_rowtype_cols (rowType : Types.typ) = 
    match rowType with 
    | `Record (fields, row_var, dual) -> fields 
    | e -> failwith "Expected a record."

let remove_list_values (l : string list) (remove : string list) = 
    List.filter (fun x -> not (List.mem x remove)) l

let update_rowtype_cols (cols : Types.field_spec_map) (rowType : Types.typ) =
    match rowType with 
    | `Record (_, row_var, dual) -> `Record (cols, row_var, dual)
    | e -> failwith "Expected a record."

let try_find p l = try Some (List.find p l) with Not_found -> None | NotFound _ -> None

let get_record_val (key : string) (r : Value.t) = 
    let columns = unbox_record r in
    let (_, value) = List.find (fun (name, value) -> name = key) columns in
    value
      
let get_field_spec_type (typ : Types.field_spec) = 
    match typ with
    | `Present t -> t
    | _ -> failwith "Expected `Present"

let records_equal recA recB =
    (* this function checks that every entry in recA is equal in recB *)
    not (List.exists (fun (name, value) -> get_record_val name recB <> value) (unbox_record recA))

let records_match_on recA recB on =
    List.for_all (fun col ->
        get_record_val col recA = get_record_val col recB) on

let contains_record (recA : Value.t) (recordsB : Value.t) =
    let recordsB = unbox_list recordsB in
    List.exists (fun recB -> records_equal recA recB) recordsB

(* Drop related methods *)
let remove_record_type_column (a : string) (r : Types.lens_col list) =
    let fields = List.filter (fun col -> get_lens_col_alias col = a) r in
    fields

let drop_record_columns (a : string list) (record : Value.t) =
    let columns = List.filter (fun (name, _) -> not (List.mem name a)) (unbox_record record) in
        box_record columns

let drop_records_columns (a : string list) (records : Value.t) =
    let records = unbox_list records in
    let records = List.map (drop_record_columns a) records in
        box_list records

let drop_record_column (a : string) (record : Value.t) =
    drop_record_columns [a] record

let join_records (m : Value.t) (n : Value.t) (on : string list) = 
    let n = drop_record_columns on n in
    let out = List.append (unbox_record m) (unbox_record n) in
        box_record out

let restore_column (drop : string) (key : string) (default : Value.t) (row : Value.t) (records : Value.t) =
    let unb_records = unbox_list records in
    let record = try_find (fun x -> records_equal (drop_record_column drop x)  row) unb_records in
    match record with
    | Some r -> r
    | None -> 
        let keyVal = get_record_val key row in 
        let record = try_find (fun x -> get_record_val key x = keyVal) unb_records in
        let dropVal = match record with
        | Some r -> get_record_val drop r
        | None -> default in
        box_record ((drop, dropVal) :: unbox_record row) 

(* record revision *)

let apply_fd_update (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : Value.t =
    (* update all columns from the right side of the functional dependency fd 
       in m with the value from n  *)
    (* assume we know that n and m have the same values for columns in left(fd) *)
    let n_cols = unbox_record n in
    let m_cols = List.map (fun (k, v) -> 
            if List.exists (fun a -> a = k) (fd_right fd) then
                let _, n_v = List.find (fun (n_k, _) -> n_k = k) n_cols in
                k, n_v
            else
                k, v
        ) (unbox_record m) in
        box_record m_cols

let is_row_cols_record_match (m : Value.t) (n : Value.t) (cols : string list) : bool =
    (* determines wether the records m and n have the same values for the columns in cols *)
    (* check if all columns in left(fd) match *)
    let is_match = 
        List.for_all (fun col -> 
            try 
                let n_v = get_record_val col m in
                let m_v = get_record_val col n in
                    n_v = m_v
            with NotFound _ -> false 
        ) cols in
    is_match

let is_fd_record_match (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : bool =
    (* checks wether two records m and n match w.r.t. the functional dependency fd *)
    is_row_cols_record_match m n (fd_left fd)

let apply_fd_record_row_revision (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : bool * Value.t =
   (* first check if the two records match w.r.t. the given functional dependency fd and if so apply the updates
      from record n to record m, otherwise return m unchanged *)
    if is_fd_record_match m n fd then
        (* if so apply fd update *)
        true, apply_fd_update m n fd
    else
        (* otherwise return record unchanged *)
        false, m

let apply_fd_record_revision (m : Value.t) (n : Value.t) (fds : Types.fn_dep list) : bool * Value.t =
    (* m of `Record and n of `List `Record *)
    List.fold_right (fun nrow (upd, mrow) ->
            List.fold_right (fun fd (upd, mrow) ->
                let upd_t, mrow = apply_fd_record_row_revision mrow nrow fd in
                upd_t || upd, mrow
            ) fds (upd, mrow)
    ) (unbox_list n) (false, m) 
