open Types
open Utility
open Value

(* Helper methods *)
let lens_sort_fn_deps (fn_dep, _, _ : Types.lens_sort) : Types.fn_dep list =
    fn_dep

let try_find p l = try Some (List.find p l) with Not_found -> None | NotFound _ -> None

let get_record_val (key : string) (r : Value.t) = 
    let columns = match r with `Record c -> c in
    let (_, value) = List.find (fun (name, value) -> name = key) columns in
    value

    (* this function assumes the two records have identical signatures, not considering order *)
let records_equal recA recB =
    not (List.exists (fun (name, value) -> get_record_val name recB <> value) (unbox_record recA))

    (* Drop related methods *)
let remove_record_column (a : string) (r : typ) =
    match r with 
    | `Record (fields, row_var, dual) -> 
        let (entry, fields) = StringMap.pop a fields in
        `Record (fields, row_var, dual)
    | _ -> failwith "Expected a record."

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

(* record revision *)

let fd_left (fd_left, _ : Types.fn_dep) = fd_left

let fd_right (_, fd_right : Types.fn_dep) = fd_right

let apply_fd_update (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : Value.t =
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

let is_fd_record_match (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : bool =
    let n_cols = unbox_record n in
    (* check if all columns in left(fd) match *)
    let is_match = List.for_all (fun (k, v) -> 
        if List.exists (fun a -> a = k) (fd_left fd) then
            let _, n_v = List.find (fun (n_k, _) -> n_k = k) n_cols in
                v = n_v
        else
            true
    ) (unbox_record m) in
        is_match

let apply_fd_record_row_revision (m : Value.t) (n : Value.t) (fd : Types.fn_dep) : bool * Value.t =
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


(* get / put operations *)

let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens
    | `LensSelect (lens, pred, sort) -> is_memory_lens lens
    | _ -> failwith ("Unknown lens (is_memory_lens) :" ^ (string_of_value lens))

let rec lens_get_mem (lens : Value.t) callfn =
    match lens with
    | `Lens _ -> failwith "Non memory lenses not implemented."
    | `LensMem (table, rtype) -> table
    | `LensDrop (lens, drop, key, def, rtype) ->
        let records = lens_get_mem lens callfn in
        let result = List.map (fun a -> drop_record_row drop a) (unbox_list records) in
          `List result
    | `LensSelect (lens, pred, sort) ->
        let records = lens_get_mem lens callfn in
        let res = List.filter (fun x -> unbox_bool (callfn pred [x])) (unbox_list records) in 
           box_list res
    | _ -> failwith "Not a lens."

let rec lens_get (lens : Value.t) callfn =
    if is_memory_lens lens then
        lens_get_mem lens callfn 
    else
        box_list [] 

let mark_found_records (n : Value.t) (data : (Value.t * bool) array) : unit = 
    Array.iteri (fun i (row, marked) -> 
        if not marked && (records_equal row n) then
            Array.set data i (row, true)
    ) data

let rec lens_put_mem (lens : Value.t) (data : Value.t) callfn =
    match lens with
    | `Lens _ -> data
    | `LensMem _ -> data
    | `LensDrop (l, drop, key, def, rtype) -> 
            let records = lens_get l callfn in
            let newRecords = List.map (fun x -> restore_column drop key def x records) (unbox_list data) in
                lens_put_mem l (box_list newRecords) callfn
    | `LensSelect (l, pred, sort) ->
            let arrData = Array.of_list (List.map (fun r -> r,false) (unbox_list data)) in
            let records = unbox_list (lens_get l callfn) in
            let output = ref [] in
            let _ = List.map (fun r -> 
                (* if the record matches P remove it *)
                if not (unbox_bool (callfn pred [r])) then
                    begin
                        let upd, r = apply_fd_record_revision r data (lens_sort_fn_deps sort) in
                        if upd then
                            mark_found_records r arrData;
                        output := r :: !output
                    end
                else
                   () 
            ) records in
            let filteredData = List.filter (fun (r,m) -> not m) (Array.to_list arrData) in
            let output = List.append !output (List.map (fun (r,m) -> r) filteredData) in
            lens_put_mem l (box_list output) callfn
    | _ -> failwith "Not a lens."

let rec lens_put (lens : Value.t) (data : Value.t) callfn =
    if is_memory_lens lens then
        lens_put_mem lens data callfn 
    else
        data

let get_fd (keys : Sugartypes.name list) (rowType : Types.typ) : Types.fn_dep =
    match rowType with `Record (fields, row_var, dual) ->
        let fields = List.fold_right (fun col columns -> StringMap.remove col columns) keys fields in
        let notkeys = StringMap.to_list (fun x y -> x) fields in
            (keys, notkeys)
    | _ -> failwith "Expected a record."

let get_phrasenode (phrase, _ : Sugartypes.phrase) =
    phrase

let get_pos (_, pos : Sugartypes.phrase) =
    pos

let get_var_name (var : Sugartypes.phrasenode) = 
    match var with
    | `Var name -> name
    | _ -> failwith "Expected a `Var type"

let get_fds (key : Sugartypes.phrase) (rowType : Types.typ) : Types.fn_dep list =
    match (get_phrasenode key) with
    | `TupleLit keys -> [get_fd (List.map (fun x -> get_var_name (get_phrasenode x))  keys) rowType]
    | `Var name -> [get_fd [name] rowType]
    | _ -> failwith "Expected a tuple or a variable."