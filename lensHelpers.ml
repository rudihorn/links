open Types
open Utility
open Value
open LensFDHelpers

(* Helper methods *)
let get_lens_type_sort (t : Types.typ) =
    match t with
    | `Lens sort -> sort
    | e -> failwith "Did not match a lens type (get_lens_sort)."

let get_lens_sort (v : Value.t) = 
    match v with
    | `Lens (a, sort) -> sort
    | `LensMem (a, sort) -> sort
    | `LensDrop  (lens, drop, key, def, sort) -> sort
    | `LensSelect (lens, pred, sort) -> sort
    | `LensJoin (lens1, lens2, on, sort) -> sort
    | e -> failwith "Did not match a lens value (get_lens_sort)."

let get_lens_sort_fn_deps (fn_dep, _, _ : Types.lens_sort) : Types.fn_dep list =
    fn_dep

let get_lens_sort_row_type (_, _, rowType : Types.lens_sort) = rowType

let get_rowtype_cols (rowType : Types.typ) = 
    match rowType with 
    | `Record (fields, row_var, dual) -> fields 
    | e -> failwith "Expected a record."

let get_lens_sort_cols_list (sort : Types.lens_sort) : string list = 
    let rowType = get_lens_sort_row_type sort in
    let cols = get_rowtype_cols rowType in
    let colsList = StringMap.to_list (fun k v -> k) cols in
        colsList

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

let records_equal recA recB =
    (* this function checks that every entry in recA is equal in recB *)
    not (List.exists (fun (name, value) -> get_record_val name recB <> value) (unbox_record recA))

let contains_record (recA : Value.t) (recordsB : Value.t) =
    let recordsB = unbox_list recordsB in
    List.exists (fun recB -> records_equal recA recB) recordsB

    (* Drop related methods *)
let remove_record_type_column (a : string) (r : typ) =
    let fields = get_rowtype_cols r in
    let (entry, fields) = StringMap.pop a fields in
        update_rowtype_cols fields r

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


(* get / put operations *)

let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens
    | `LensSelect (lens, pred, sort) -> is_memory_lens lens
    | `LensJoin (lens1, lens2, on, sort) -> is_memory_lens lens1 || is_memory_lens lens2
    | _ -> failwith ("Unknown lens (is_memory_lens) :" ^ (string_of_value lens))

let rec lens_get_mem (lens : Value.t) callfn =
    match lens with
    | `Lens _ -> failwith "Non memory lenses not implemented."
    | `LensMem (table, rtype) -> table
    | `LensDrop (lens, drop, key, def, rtype) ->
        let records = lens_get_mem lens callfn in
        let result = List.map (fun a -> drop_record_column drop a) (unbox_list records) in
          `List result
    | `LensSelect (lens, pred, sort) ->
        let records = lens_get_mem lens callfn in
        let res = List.filter (fun x -> unbox_bool (callfn pred [x])) (unbox_list records) in 
           box_list res
    | `LensJoin (lens1, lens2, on, sort) ->
        let records1 = lens_get_mem lens1 callfn in
        let records2 = lens_get_mem lens2 callfn in
        let output = List.map (fun r1 -> 
            let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 on) (unbox_list records2) in
            List.map (fun r2 ->  join_records r1 r2 on) rows
        ) (unbox_list records1) in
        box_list (List.concat output)
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


let apply_fd_merge_record_revision (n : Value.t) (m : Value.t) (fds : Types.fn_dep list) = 
    (* `List `Record * `List `Record * fds *)
    let arrM = Array.of_list (List.map (fun r -> r,false) (unbox_list m)) in
    let output = ref [] in
    let _ = List.map (fun r ->
        let upd, r = apply_fd_record_revision r m fds in
            mark_found_records r arrM;
            output := r :: !output
    ) (unbox_list n) in
    let filteredData = List.filter (fun (r,m) -> not m) (Array.to_list arrM) in
    let output = List.append !output (List.map (fun (r,m) -> r) filteredData) in
        (box_list output)

let rec lens_put_delta  (lens : Value.t) (data : (Value.t * int) list) callfn = 
    match lens with
    | `Lens _ ->  data
    | `LensMem _ -> data
    | `LensSelect (l, pred, sort) ->
        data
    | `LensJoin  (l1, l2, on, sort) ->
        data
    | _ -> failwith "Unsupported lens."

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
                        let upd, r = apply_fd_record_revision r data (get_lens_sort_fn_deps sort) in
                        if upd then
                            begin
                                if not (unbox_bool (callfn pred[r])) then
                                    mark_found_records r arrData
                            end
                        else
                            output := r :: !output
                    end
                else
                   () 
            ) records in
            let filteredData = List.filter (fun (r,m) -> not m) (Array.to_list arrData) in
            let output = List.append !output (List.map (fun (r,m) -> r) filteredData) in
            lens_put_mem l (box_list output) callfn 
    | `LensJoin (l1, l2, on, sort) ->
            let fds = get_lens_sort_fn_deps sort in
            let _ = debug_print_fd_tree (get_fd_tree fds) in
            let sort_cols = get_lens_sort_cols_list sort in
            let l1_sort = get_lens_sort l1 in
            let l1_cols = get_lens_sort_cols_list l1_sort in
            let remcols1 = remove_list_values sort_cols l1_cols in
            let rec1 = lens_get l1 callfn in
            let rec1 = apply_fd_merge_record_revision rec1 (drop_records_columns remcols1 data) fds in
            let l2_sort = get_lens_sort l2 in
            let l2_cols = get_lens_sort_cols_list l2_sort in
            let remcols2 = remove_list_values sort_cols l2_cols in
            let rec2 = lens_get l2 callfn in
            let rec2 = apply_fd_merge_record_revision rec2 (drop_records_columns remcols2 data) fds in
            let removed = List.map (fun r1 ->
                let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 on) (unbox_list rec2) in
                let rows = List.map (fun r2 -> join_records r1 r2 on) rows in
                let rows = List.filter (fun r -> not (contains_record r data)) rows in
                    rows
            ) (unbox_list rec1) in
            let removed = List.concat removed in
            let not_on_cols = remove_list_values sort_cols on in 
            let removed_left, removed_any = List.partition (fun r -> contains_record (drop_record_columns not_on_cols r) data) removed in
            let rec1 = List.filter (fun r -> not (contains_record r (box_list removed_left))) (unbox_list rec1) in
            let rec1 = lens_put_mem l1 (box_list rec1) callfn in
            let rec2 = List.filter (fun r -> not (contains_record r (box_list removed_any))) (unbox_list rec2) in
            let rec2 = lens_put_mem l2 (box_list rec2) callfn in
                box_record (["t1", rec1; "t2", rec2])
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

let get_phrase_columns (key : Sugartypes.phrase) : string list = 
    match (get_phrasenode key) with
    | `TupleLit keys -> List.map (fun x -> get_var_name (get_phrasenode x))  keys
    | `Var name -> [name]
    | _ -> failwith "Expected a tuple or a variable."

let get_fds (key : Sugartypes.phrase) (rowType : Types.typ) : Types.fn_dep list =
    [get_fd (get_phrase_columns key) rowType]

let join_lens_sort (sort1 : Types.lens_sort) (sort2 : Types.lens_sort) (key : Sugartypes.phrase) = 
    let on_columns = get_phrase_columns key in
    let cols1 = get_rowtype_cols (get_lens_sort_row_type sort1) in
    let cols2 = get_rowtype_cols (get_lens_sort_row_type sort2) in
    if List.for_all (fun onc ->
        (StringMap.find onc cols1) = (StringMap.find onc cols2)) on_columns then
        let union = StringMap.fold (fun c v output -> if StringMap.mem c output then output else StringMap.add c v output) cols2 cols1 in
        let rowType = update_rowtype_cols union (get_lens_sort_row_type sort1) in
        let fn_deps = List.append (get_lens_sort_fn_deps sort1) (get_lens_sort_fn_deps sort2) in
            (fn_deps, "", rowType)
    else
        failwith "The key does not match between the two lenses."
