open Types
open Utility
open Value
open LensFDHelpers
open LensQueryHelpers
open LensRecordHelpers

(* Helper methods *)
let get_record_type_sort_cols (tableName : string) (typ : Types.typ) = 
  let cols = get_rowtype_cols typ in
  let cols = StringMap.to_list (fun k v -> {table = tableName; name = k; alias = k; typ = get_field_spec_type v; present = true;}) cols in
  cols

let get_lens_sort_cols_list (sort : Types.lens_sort) : string list = 
    let rowType = get_lens_sort_row_type sort in
    let cols = get_rowtype_cols rowType in
    let colsList = StringMap.to_list (fun k v -> k) cols in
        colsList

let get_lens_type_sort (t : Types.typ) =
    match t with
    | `Lens sort -> sort
    | e -> failwith "Did not match a lens type (get_lens_sort)."

let get_lens_sort (v : Value.t) = 
    match v with
    | `Lens (a, sort) -> sort
    | `LensMem (a, sort) -> sort
    | `LensDrop (lens, drop, key, def, sort) -> sort
    | `LensSelect (lens, pred, sort) -> sort
    | `LensJoin (lens1, lens2, on, sort) -> sort
    | e -> failwith "Did not match a lens value (get_lens_sort)."

let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens
    | `LensSelect (lens, pred, sort) -> is_memory_lens lens
    | `LensJoin (lens1, lens2, on, sort) -> is_memory_lens lens1 || is_memory_lens lens2
    | _ -> failwith ("Unknown lens (is_memory_lens) :" ^ (string_of_value lens))

(* get / put operations *)

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
        let res = List.filter (fun x -> unbox_bool (calculate_predicate_rec pred x)) (unbox_list records) in 
           box_list res
    | `LensJoin (lens1, lens2, on, sort) ->
        let records1 = lens_get_mem lens1 callfn in
        let records2 = lens_get_mem lens2 callfn in
        let on = List.map (fun (a, _, _) -> a) on in
        let output = List.map (fun r1 -> 
            let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 on) (unbox_list records2) in
            List.map (fun r2 ->  join_records r1 r2 on) rows
        ) (unbox_list records1) in
        box_list (List.concat output)
    | _ -> failwith "Not a lens."


let rec lens_get_query (lens : Value.t) =
  match lens with
  | `Lens (((db, _), table, _, _), sort) -> 
        let cols = get_lens_sort_cols sort in
        {
            tables = [table, table];
            cols = cols;
            pred = None;
            db = db;
        }
  | `LensSelect (lens, pred, sort) ->
        let query = lens_get_query lens in
        { query with pred = Some pred }
        (* get_lens_sort_row_type sort *)
  | `LensJoin (lens1, lens2, on, sort) ->
        let q1 = lens_get_query lens1 in
        let q2 = lens_get_query lens2 in
        (* all table names must be unique, rename them *)
        let tables2 = List.map (fun (n2, al2) -> 
            try 
                let tbl = List.find (fun (n1,al1) -> n1 = n2) q1.tables in
                failwith "Cannot reuse a table twice in a join query!"
            with
                NotFound _ -> (n2, al2)
        ) q2.tables in
        let tables = List.append q1.tables q2.tables in
        let cols = get_lens_sort_cols sort in
        if (q1.db <> q2.db) then
            failwith "Only single database expressions supported."
        else
            {tables = tables; cols = cols; pred = get_lens_sort_pred sort; db = q1.db}
  | _ -> failwith "Unsupported lens for query"

(* BUG: Lists can be too big for List.map; need to be careful about recursion *)
let rec lens_get (lens : Value.t) callfn =
    if is_memory_lens lens then
        lens_get_mem lens callfn 
    else
        let _ = Debug.print "getting tables" in
        let query = lens_get_query lens in
        let sql = construct_select_query query  in
        let mappings = List.map (fun c -> get_lens_col_alias c, get_lens_col_type c) query.cols in
        let res = execute_select mappings sql query.db in
        let _ = Debug.print sql in
        res

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
                if not (unbox_bool (calculate_predicate_rec pred r)) then
                    begin
                        let upd, r = apply_fd_record_revision r data (get_lens_sort_fn_deps sort) in
                        if upd then
                            begin
                                if not (unbox_bool (calculate_predicate_rec pred r)) then
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
            let oldOn = List.map (fun (a, _, _) -> a) on in
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
                let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 oldOn) (unbox_list rec2) in
                let rows = List.map (fun r2 -> join_records r1 r2 oldOn) rows in
                let rows = List.filter (fun r -> not (contains_record r data)) rows in
                    rows
            ) (unbox_list rec1) in
            let removed = List.concat removed in
            let not_on_cols = remove_list_values sort_cols oldOn in 
            let removed_left, removed_any = List.partition (fun r -> contains_record (drop_record_columns not_on_cols r) data) removed in
            let rec1 = List.filter (fun r -> not (contains_record r (box_list removed_left))) (unbox_list rec1) in
            let rec1 = lens_put_mem l1 (box_list rec1) callfn in
            let rec2 = List.filter (fun r -> not (contains_record r (box_list removed_any))) (unbox_list rec2) in
            let rec2 = lens_put_mem l2 (box_list rec2) callfn in
                box_record (["t1", rec1; "t2", rec2])
    | _ -> failwith "Not a lens."

type delete_side = [
    | `Left
    | `Any
    | `Right
    | `Both
]

let lens_debug_delta (delta : (Value.t * int) list) = 
    List.map (fun (t,m) -> Debug.print (string_of_int m ^ ": " ^ string_of_value t)) delta

let rec lens_delta_put_ex (lens : Value.t) (data : (Value.t * int) list) =
    match lens with 
    | `Lens _ -> 
        let _ = lens_debug_delta data in data 
    | `LensMem _ -> 
        let _ = Debug.print "Put Lens Data:" in 
        let _ = lens_debug_delta data in data
    | `LensDrop (l, drop, key, def, rtype) ->
            let query_phrase = fun t key -> create_phrase_equal (create_phrase_var key) (create_phrase_constant_of_record_col t key) in
            let data = List.map (fun (t,m) -> 
                    let col = lens_get (`LensSelect (l, query_phrase t key, get_lens_sort(lens))) None in
                    let t = unbox_record t in
                    let t = match unbox_list col with
                    | [] -> box_record ((drop, def) :: t)
                    | x :: xs -> box_record ((drop, get_record_val drop x) :: t) in
                    t,m
                ) data in
                lens_delta_put_ex l data 
    | `LensSelect (l, pred, sort) ->
            let data = List.map (fun (t,m) ->
                match m with
                | -1 -> [(t,m)]
                | 0 -> [(t,m)]
                | +1 -> 
                    let fds = get_lens_sort_fn_deps sort in
                    let gen_equals = fun fd ->
                        create_phrase_equal (create_phrase_var fd) (create_phrase_constant_of_record_col t fd) in
                    let gen_pred = fun fd -> 
                        let key = fd_left fd in
                        let closure = get_fd_transitive_closure key fds in
                        let closure = List.map (fun a -> (a,get_record_val a t)) closure in
                        let keyCheck = List.fold_left (fun a fd -> create_phrase_and a (gen_equals fd)) (gen_equals (List.hd key)) (List.tl key) in
                        let predCheck = replace_var pred closure in
                            create_phrase_tuple (create_phrase_and keyCheck predCheck) in
                    let upd_pred = List.fold_left (fun a fd -> create_phrase_or a (gen_pred fd)) (gen_pred (List.hd fds)) (List.tl fds) in
                    let query_phrase = create_phrase_and (create_phrase_not pred) (create_phrase_tuple upd_pred) in
                    (* let _ = Debug.print (construct_query query_phrase) in
                    let _ = debug_print_fd_tree (get_fd_tree fds) in *)
                    let others = lens_get (`LensSelect (l, query_phrase, sort)) None in
                    let others = List.map (fun x -> (x,-1)) (unbox_list others) in
                    let _ = Debug.print (string_of_int (List.length others)) in
                    (t,m) :: others
                | _ -> failwith "Unexpected multiplicity"
            ) data in
            let data = List.flatten data in
            lens_delta_put_ex l data
    | `LensJoin (l1, l2, on, sort) ->
        let on = List.map (fun (a,_,_) -> a) on in
        let t3 = List.map (fun (t,m) -> 
            let recs : (Value.t * int * delete_side) list =  
                match m with
                | -1 -> [if (List.exists (fun (t1,m1) -> m >= 0 && records_match_on t t1 on)  data) then (t, m, `Left) else (t, m, `Any)]
                | 0 -> [(t,m,`Both)]
                | 1 -> [if (List.exists (fun (t1, m1) -> m = 0 && records_match_on t t1 on) data) then (t,m, `Left) else (t, m, `Both)]
                | _ -> failwith ("Unexpected multiplicity") in
            recs
        ) data in
        let project_lens = (fun l t -> 
            let l_sort = get_lens_sort l in
            let l_cols = get_lens_sort_cols_list l_sort in
            let rem_cols = remove_list_values (get_lens_sort_cols_list sort) l_cols in
            List.map (fun (row,t) -> drop_record_columns rem_cols row,t) t
            ) in
        let t3 = List.flatten t3 in
        let t1 = List.filter (fun (t,m,s) -> s = `Left || s = `Both || (s = `Any)) t3 in
        let t1 = List.map (fun (t,m,s) -> (t,m)) t1 in
        let t1 = project_lens l1 t1 in
        let t2 = List.filter (fun (t,m,s) -> s = `Right || s = `Both || (s = `Any && false)) t3 in
        let t2 = List.map (fun (t,m,s) -> (t,m)) t2 in
        let t2 = project_lens l2 t2 in
        let t2 = List.sort_uniq (fun (r1,m1) (r2,m2) -> if (records_equal r1 r2) then 0 else 1) t2 in
        let t1 = lens_delta_put_ex  l1 t1 in
        let t2 = lens_delta_put_ex l2 t2 in
        t2
    | _ -> failwith "Not a lens."

let lens_delta_put (lens : Value.t) (dataOrig : Value.t) (data : Value.t) =
    let dataOrig = unbox_list dataOrig in
    let data = unbox_list data in
    let delta = List.map (fun t -> if List.exists (records_equal t) dataOrig then (t,0) else (t,1)) data in
    let deltaRemoved = List.filter (fun t -> not (List.exists (records_equal t) data)) dataOrig in
    let delta = List.append delta (List.map (fun t -> (t,-1)) deltaRemoved) in
    let _ = Debug.print "Input delta: "; lens_debug_delta delta in
    lens_delta_put_ex lens delta

  let rec lens_put (lens : Value.t) (data : Value.t) callfn =
    let delta = lens_delta_put lens (lens_get lens callfn) data in
    if is_memory_lens lens then
        lens_put_mem lens data callfn 
    else
        data

let get_fd (keys : Operators.name list) (rowType : Types.typ) : Types.fn_dep =
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

let select_lens_sort (sort : Types.lens_sort) (pred : lens_phrase) : Types.lens_sort = 
    let (fds, oldPred, cols) = sort in
    let pred = match oldPred with 
    | None -> pred
    | Some oldPred -> create_phrase_and (create_phrase_tuple pred) (create_phrase_tuple oldPred) in
    let pred = Some pred in
    (fds, pred, cols)

let join_lens_sort (sort1 : Types.lens_sort) (sort2 : Types.lens_sort) (on_columns : string list) = 
    let get_alias = get_lens_col_alias in
    let get_type = get_lens_col_type in
    let rec get_new_alias alias columns num = 
        let nal = alias ^ "_" ^ string_of_int num in
        if List.exists (fun c -> get_alias c = nal) columns then
            get_new_alias alias columns (num + 1)
        else 
            nal in
    let on_match = List.for_all (fun onc -> 
            let c2 = get_lens_sort_col_by_alias sort2 onc in
            let c1 = get_lens_sort_col_by_alias sort1 onc in
            match c1, c2 with
            | Some c1, Some c2 -> get_type c1 = get_type c2
            | _ -> false) on_columns in
    if on_match then
        let union, join_renames = List.fold_left (fun (output, jrs) c-> 
            let c2 = get_lens_col_by_alias output (get_alias c) in
            match c2 with 
            | None -> c :: output, jrs
            | Some c2 -> 
                let _ = Debug.print ("duplicate " ^ c.alias) in
                let is_on = List.mem (get_alias c) on_columns in
                if is_on then
                    let new_alias = get_new_alias c.alias output 1 in
                    let _ = Debug.print ("alias " ^ c.alias ^ " -> " ^ new_alias) in
                    {c with alias = new_alias; present = false;} :: output, (c.alias, new_alias) :: jrs
                else 
                    (set_lens_col_alias c (get_new_alias (get_alias c) output 1)) :: output, jrs
        ) (get_lens_sort_cols sort1, []) (get_lens_sort_cols sort2) in
        let pred = match get_lens_sort_pred sort1, get_lens_sort_pred sort2 with
        | None, None -> None
        | Some p1, None -> Some p1
        | None, Some p2 -> Some (rename_var p2 join_renames)
        | Some p1, Some p2 -> Some (create_phrase_and (create_phrase_tuple p1) (create_phrase_tuple (rename_var p2 join_renames))) in
        let join_pred = List.fold_left (fun pred (alias, newalias) -> 
            let jn = create_phrase_equal (create_phrase_var alias) (create_phrase_var newalias) in
            match pred with Some p -> Some (create_phrase_and p jn) | None -> Some jn
        ) pred join_renames in
        let fn_deps = List.append (get_lens_sort_fn_deps sort1) (get_lens_sort_fn_deps sort2) in
        (* determine the on column renames as a tuple (join, left, right) *)
        let jrs = List.map (fun on -> 
            let left = on in
            let (_, right) = List.find (fun (a,b) -> a = on) join_renames in
            on, left, right) on_columns in
        (fn_deps, join_pred, union), jrs 
     else 
        failwith "The key does not match between the two lenses."

(* let join_lens_sort (sort1 : Types.lens_sort) (sort2 : Types.lens_sort) (key : Sugartypes.phrase) = 
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
*)