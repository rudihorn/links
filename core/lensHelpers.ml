open Types
open Utility
open Value
open LensFDHelpers
open LensQueryHelpers
open LensSetOperations
open LensRecordHelpers

let query_timer = ref 0
let query_count = ref 0

(*** Lenses Force Memory ***)
let lens_force_mem_enabled = Settings.add_bool ("lens_force_mem", false, `User)


(** print a debug message if debugging is enabled *)
let print message =
  (if false then print_endline message)

let ensure_lenses_enabled () = 
  if Settings.get_value Basicsettings.RelationalLenses.relational_lenses then
    ()
  else
    failwith "Code uses relational lenses, but relational lenses are not enabled. Please set the relational lenses flag."


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
    | `LensJoin (lens1, lens2, on, _, _, sort) -> sort
    | e -> failwith "Did not match a lens value (get_lens_sort)."

let rec is_memory_lens (lens : Value.t) =
    match lens with
    | `Lens _ -> false
    | `LensMem _ -> true
    | `LensDrop (lens, drop, key, def, rtype) -> is_memory_lens lens
    | `LensSelect (lens, pred, sort) -> is_memory_lens lens
    | `LensJoin (lens1, lens2, on, _, _, sort) -> is_memory_lens lens1 || is_memory_lens lens2
    | _ -> failwith ("Unknown lens (is_memory_lens) :" ^ (string_of_value lens))

(* get / put operations *)

let rec get_primary_key (lens : Value.t) =
    match lens with 
    | `Lens (a, sort) -> 
        let fds = LensSort.fundeps sort in
        let fd = FunDepSet.min_elt fds in
        let left = FunDep.left fd in
        left
    | `LensMem (a, sort) ->  
        let fds = LensSort.fundeps sort in
        let fd = FunDepSet.min_elt fds in
        let left = FunDep.left fd in
        left
    | `LensDrop (lens, _, _, _, _) -> get_primary_key lens
    | `LensSelect (lens, _, _) -> get_primary_key lens
    | `LensJoin (lens1, _, _, _, _, _) -> (* right table has to be defined by left table *) get_primary_key lens1 
    | _ -> failwith ("Unknown lens (get_primary_key) : " ^ (string_of_value lens))

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
    | `LensJoin (lens1, lens2, on, left, right, sort) ->
        let records1 = lens_get_mem lens1 callfn in
        let records2 = lens_get_mem lens2 callfn in
        let on = List.map (fun (a, _, _) -> a) on in
        let output = List.map (fun r1 -> 
            let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 (ColSet.of_list on)) (unbox_list records2) in
            List.map (fun r2 ->  join_records r1 r2 on) rows
        ) (unbox_list records1) in
        box_list (List.concat output)
    | _ -> failwith "Not a lens."

let rec lens_get_db (lens : Value.t) =
    match lens with 
    | `Lens (((db, _), _, _, _), _) -> db
    | `LensDrop (l, _, _, _, _) -> lens_get_db l
    | `LensSelect (lens, _, _) -> lens_get_db lens
    | `LensJoin (l1, _, _, _, _, _) -> lens_get_db l1
    | _ -> failwith "Unsupported lens for get db."

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
  | `LensJoin (lens1, lens2, on, left, right, sort) ->
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


let lens_get_cols (lens : Value.t) =
    let sort = get_lens_sort lens in
    let cols = get_lens_sort_cols sort in
    let cols = List.filter (fun a -> a.present) cols in
    List.map get_lens_col_alias cols

(* BUG: Lists can be too big for List.map; need to be careful about recursion *)
let rec lens_get (lens : Value.t) callfn =
    if is_memory_lens lens then
        lens_get_mem lens callfn 
    else
        let _ = Debug.print "getting tables" in
        let sort = get_lens_sort lens in
        let db = lens_get_db lens in
        let cols = (get_lens_sort_cols sort) in
        (* print_endline (ListUtils.print_list (get_lens_sort_cols_list sort)); *)
        let sql = construct_select_query_sort db sort in
        (* let _ = print_endline sql in *)
        (* let query = lens_get_query lens in
        let sql = construct_select_query query  in *)
        let mappings = List.map (fun c -> get_lens_col_alias c, get_lens_col_type c) cols in
        let _ = Debug.print sql in
        let res = Debug.debug_time_out 
            (fun () -> execute_select mappings sql db) 
            (fun time -> query_timer := !query_timer + time; query_count := !query_count + 1) in
        res


let rec lens_put_delta  (lens : Value.t) (data : (Value.t * int) list) callfn = 
    match lens with
    | `Lens _ ->  data
    | `LensMem _ -> data
    | `LensSelect (l, pred, sort) ->
        data
    | `LensJoin  (l1, l2, on, left, right, sort) ->
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
                        let upd, r = apply_fd_record_revision r data (LensSort.fundeps sort) in
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
    | `LensJoin (l1, l2, on, left, right, sort) ->
            let oldOn = List.map (fun (a, _, _) -> a) on in
            let fds = LensSort.fundeps sort in
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
                let rows = List.filter (fun r2 -> is_row_cols_record_match r1 r2 (ColSet.of_list oldOn)) (unbox_list rec2) in
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
    List.map (fun (t,m) -> print (string_of_int m ^ ": " ^ string_of_value t)) delta

let project_lens (l : Value.t) (t : (Value.t * int) list) = 
    let l_sort = get_lens_sort l in
    let l_cols = get_lens_sort_cols l_sort in
    let cols = ColSet.of_list (List.map (fun c -> c.alias) l_cols) in
    List.map (fun (row,t) -> project_record_columns cols row,t) t

let is_update_row data prim cols (t,m) = 
    if m = 0 then
        false
    else
        let sameleft = fun t2 -> records_match_on t t2 prim in
        let diffright = fun t2 -> not (records_match_on t t2 cols) in
        List.exists (fun (t',m') -> m = - m && sameleft t' && diffright t') data

let select_lens_sort (sort : Types.lens_sort) (pred : lens_phrase) : Types.lens_sort =
    let oldPred = LensSort.predicate sort in
    let pred = Phrase.combine_and oldPred (Some pred) in
    (LensSort.fundeps sort, pred, LensSort.cols sort)

let lens_select (lens : Value.t) (phrase : Types.lens_phrase) =
    let sort = get_lens_sort lens in
    let sort = select_lens_sort sort phrase in
    `LensSelect (lens, phrase, sort) 

let lens_get_select (lens : Value.t) (phrase : Types.lens_phrase) =
    lens_get (lens_select lens phrase) None

let lens_get_select_opt (lens : Value.t) (phrase : Types.lens_phrase option) =
    match phrase with
    | None -> lens_get lens ()
    | Some phrase  -> lens_get_select lens phrase

let rec calculate_fd_changelist (fds : FunDepSet.t) (data : (Value.t * int) list) =
    let additions = List.filter (fun (t,m) -> m = +1) data in
    let additions = List.map (fun (t,m) -> t) additions in
    (* get the key of the row for finding complements *)
    let rec loop fds =
        if FunDepSet.is_empty fds then
            []
        else
            let fd = get_fd_root fds in 
            let fdl, fdr = FunDep.left fd, FunDep.right fd in
            let changeset = List.map (fun t ->
                (Record.project t fdl, Record.project t fdr)) additions in
            let fds = FunDepSet.remove fd fds in
            (fd, changeset) :: loop fds in
    let res = loop fds in
    res

let query_exists (lens : Value.t) phrase =
    let sort = get_lens_sort lens in
    let sort = select_lens_sort sort phrase in
    if is_memory_lens lens then
        let res = lens_get (`LensSelect (lens, phrase, sort)) None in
        unbox_list res <> []
    else
        let db = lens_get_db lens in
        let sql = construct_select_query_sort db sort in
        let sql = "SELECT EXISTS(" ^ sql ^ ") AS t" in
        let mappings = ["t", `Primitive `Bool] in
        let res = Debug.debug_time_out 
            (fun () -> execute_select mappings sql db)
            (fun time -> query_timer := !query_timer + time; query_count := !query_count + 1) in
        let _ = Debug.print sql in
        let (_,v)::_ = unbox_record (List.hd (unbox_list res)) in
        unbox_bool v


let can_remove_phrase (sort : Types.lens_sort) (on : (string * string * string) list) (row : Value.t) (data : (Value.t * int) list) =
    let on_simp = List.map (fun (a,_,_) -> a) on in
    let fds = LensSort.fundeps sort in
    let fd = get_fd_root fds in
    let key = FunDep.left fd in
    (* phrase_on tries to find all records where on is identical to the values of row *)
    let phrase_on = Phrase.matching_cols (ColSet.of_list on_simp) row in
    (* phrase not added changes *)
    let changelist = calculate_fd_changelist fds data in
    let rec ignore_change col =
        let fd = FunDepSet.get_defining fds col in
        let (_,changes) = List.find (fun (fd', changes) -> fd = fd') changelist in
        let phrases = List.map (fun (chl, chr) ->
                Phrase.negate (OptionUtils.val_of (Phrase.matching_cols (FunDep.left fd) chl))
            ) changes in
        let phrases = Phrase.combine_and_l phrases in
        if ColSet.subset key (FunDep.left fd) then
            phrases
        else 
            Phrase.combine_and (ignore_change (FunDep.left fd)) phrases in
    let phrase_not_changed = ignore_change (ColSet.of_list on_simp) in
    (* phrase_not_removed finds all records which aren't marked for deletion *)
    let removed = List.filter (fun (r,m) -> m = -1 && Record.match_on r row on_simp) data in
    let removed = List.map (fun (r,m) -> r) removed in
    let dels = List.filter (fun r -> 
        let compl = List.filter (fun (r',m) -> m = +1 && Record.match_on r r' (ColSet.elements key)) data in
        compl = []
    ) removed in
    let phrase_not_removed = List.fold_left (fun phrase delrow ->
        let term = Phrase.negate (OptionUtils.val_of (Phrase.matching_cols key delrow)) in
        Phrase.combine_and phrase (Some term)
    ) None dels in
    (* combine all criteria *)
    let phrase = Phrase.combine_and_l_opt [ 
        phrase_on; 
        phrase_not_removed; 
        phrase_not_changed; 
    ] in
    phrase

let remove_select_phrase (sort : Types.lens_sort) (predicate : Types.lens_phrase) (data : (Value.t * int) list) =
    let fds = LensSort.fundeps sort in
    let fd = get_fd_root fds in
    let key = FunDep.left fd in
    (* phrase_on tries to find all records where on is identical to the values of row *)
    let phrase_not_matched = Phrase.negate (Phrase.tuple predicate)  in
    (* phrase not added changes *)
    let changelist = calculate_fd_changelist fds data in
    (* for a specific column find an expression which calculates its actual value *)
    let rec var_expr col curCols vals (otherwise : Types.lens_phrase) = 
        let (fd, defch) = List.find (fun (fd, changes) ->
            ColSet.subset curCols (FunDep.right fd)) changelist in
        let changes = OptionUtils.opt_app (fun vals -> List.map (fun (chl, chr) -> 
            let (_, res) = List.find (fun (chl', chr') -> Record.match_on chr chl' (ColSet.elements (FunDep.right fd))) vals in
            (chl, res)
        ) defch) defch vals in
        let phrase = `Case (None, (List.map (fun (chl, chr) -> 
                OptionUtils.val_of (Phrase.matching_cols (FunDep.left fd) chl), Phrase.constant (constant_of_value (Record.column col chr))) changes
            ),otherwise) in
        if ColSet.subset key (FunDep.left fd) then
            phrase
        else
            var_expr col (FunDep.left fd) (Some changes) phrase in
    (* for every used column, determine this expression *)
    let used_vars = Phrase.get_vars predicate in
    let varmap = List.map (fun col ->
        col, var_expr col (ColSet.of_list [col]) None (Phrase.var col)
    ) (ColSet.elements used_vars) in
    (* replace every used var instance in the predicate with the new value *)
    let now_match_predicate = Phrase.traverse predicate (fun expr ->
        match expr with
        | `Var n -> 
            let (_, repl) = List.find (fun (a,_) -> a = n) varmap in
            repl
        | _ -> expr
    ) in
    (* phrase_not_removed finds all records which aren't marked for deletion *)
    let removed = List.filter (fun (r,m) -> m = -1) data in
    let removed = List.map (fun (r,m) -> r) removed in
    let dels = List.filter (fun r -> 
        let compl = List.filter (fun (r',m) -> m = +1 && Record.match_on r r' (ColSet.elements key)) data in
        compl = []
    ) removed in
    let phrase_not_removed = List.fold_left (fun phrase delrow ->
        let term = Phrase.negate (OptionUtils.val_of (Phrase.matching_cols key delrow)) in
        Phrase.combine_and phrase (Some term)
    ) None dels in
    (* combine all criteria *)
    let phrase = Phrase.combine_and_l_opt [ 
        Some phrase_not_matched; 
        phrase_not_removed; 
        Some now_match_predicate; 
    ] in
    phrase

let get_fd (keys : Operators.name list) (rowType : Types.typ) : Types.fundep =
    match rowType with `Record (fields, row_var, dual) ->
        let fields = List.fold_right (fun col columns -> StringMap.remove col columns) keys fields in
        let keys = ColSet.of_list keys in
        let notkeys = StringMap.to_list (fun x y -> x) fields in
        let notkeys = ColSet.of_list notkeys in
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

let get_fds (key : Sugartypes.phrase) (rowType : Types.typ) : Types.fundepset =
    FunDepSet.of_list [get_fd (get_phrase_columns key) rowType]



let join_lens_should_swap (sort1 : Types.lens_sort) (sort2 : Types.lens_sort) (on_columns : string list) =
    let fds1 = LensSort.fundeps sort1 in
    let fds2 = LensSort.fundeps sort2 in
    let on_cols = ColSet.of_list on_columns in
    let covers fds sort =
        let fdcl = get_fd_transitive_closure on_cols fds in
        let other = LensSort.present_cols sort |> List.map (LensCol.alias) |> ColSet.of_list in
        (* print_endline (ColSet.Show_t.show fdcl ^ " = " ^ ColSet.Show_t.show (other)); *)
        ColSet.equal other fdcl in
    if covers fds2 sort2 then
        false
    else if covers fds1 sort1 then
        true
    else
        failwith "One of the tables needs to be defined by the join column set."

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
                (* let _ = Debug.print ("duplicate " ^ c.alias) in *)
                let is_on = List.mem (get_alias c) on_columns in
                if is_on then
                    let new_alias = get_new_alias c.alias output 1 in
                    (* let _ = Debug.print ("alias " ^ c.alias ^ " -> " ^ new_alias) in *)
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
        let fn_deps = FunDepSet.union (LensSort.fundeps sort1) (LensSort.fundeps sort2) in
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


