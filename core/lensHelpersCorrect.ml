open Types
open Value
open Utility
open LensQueryHelpers
open LensHelpers
open LensFDHelpers
open LensSetOperations
open LensRecordHelpers



let rec calculate_fd_changelist (fds : FunDepSet.t) (data : SortedRecords.recs) =
    let additions = data.plus_rows in
    (* get the key of the row for finding complements *)
    let rec loop fds =
        if FunDepSet.is_empty fds then
            []
        else
            let fd = get_fd_root fds in 
            let fdl, fdr = FunDep.left fd, FunDep.right fd in
            let cols_l = ColSet.elements fdl in
            let cols_r = ColSet.elements fdr in
            let fdl_map = SortedRecords.get_cols_map data cols_l in
            let fdr_map = SortedRecords.get_cols_map data cols_r in
            let map = fun r -> fdl_map r, fdr_map r in
            let changeset = Array.to_list (Array.map map data.plus_rows) in
            (* remove duplicates and sort *)
            let changeset = List.sort_uniq (fun (a,_) (a',_) -> SortedRecords.compare a a') changeset in
            let fds = FunDepSet.remove fd fds in
            ((cols_l, cols_r), changeset) :: loop fds in
    let res = loop fds in
    (* reverse the list, so that the FD roots appear first *)
    List.rev res

let matches_change changes = 
    let is_changed ((cols_l, cols_r),(vals)) =
        List.fold_left (fun phrase (on,_) ->
            let term = Phrase.matching_cols_simp cols_l on in
            Phrase.combine_or phrase term) None vals in
    List.fold_left (fun phrase change ->
        let term = is_changed change in
        Phrase.combine_or phrase term) None changes

let get_changes (lens : Value.t) (data : SortedRecords.recs) =
    let sort = get_lens_sort lens in
    let fds = get_lens_sort_fn_deps sort in
    let changelist = calculate_fd_changelist fds data in
    let phrase = matches_change changelist in
    let res = lens_get_select_opt lens phrase in
    let res = SortedRecords.construct_cols (lens_get_cols lens) res in
    let changes = List.map (fun ((cols_l,cols_r),l) -> 
        (* get a map from simp rec to col value *)
        let col_maps = List.map (SortedRecords.get_col_map res) cols_l in
        let col_maps = List.flatten (List.map (fun mp -> match mp with None -> [] | Some a -> [a]) col_maps) in
        (* get a map from col name to change value *)
        let (val_maps,_) = List.fold_left (fun (maps,fn) _ -> 
            (fun a -> List.hd (fn a)) :: maps, (fun a -> List.tl (fn a))) ([], fun a -> a) cols_l in
        let maps = List.combine col_maps val_maps in
        (* get a function which compares column with change *)
        let comp = List.fold_left (fun a (mp1, mp2) -> 
            fun record change_key -> mp1 record = mp2 change_key && a record change_key) (fun a b -> true) maps in
        comp
    ) changelist in
    let apply_changes = List.map (fun ((cols_l, cols_r),l) ->
        let rec upd cols =
            match cols with 
            | [] -> fun r target -> []
            | x :: xs -> 
                let fn = upd xs in
                let map = SortedRecords.get_col_map_list cols_r x in
                match map with 
                | None -> (* the column does not have to be replaced *)
                        fun (y :: ys) target -> y :: fn ys target 
                | Some mp -> (* the column has been found, replace *)
                        fun (y :: ys) target -> 
                            mp target :: fn ys target
                in 
        upd res.columns 
    ) changelist in
    let update arr = Array.map (fun r ->
        let r' = List.fold_left (fun r ((check, update),(_, changes)) -> 
            let upd = List.find_opt (fun (left, right) -> check r left) changes in
            match upd with
            | None -> r
            | Some (left, right) -> update r right
        ) r (List.combine (List.combine changes apply_changes) changelist) in
        (r', r)
        (* print_endline (string_of_value (box_list r) ^ " to " ^ string_of_value (box_list r'));
        r' *)
    ) arr in
    let res2 = update res.plus_rows in
    let res2 = List.flatten (List.map (fun (r, r') -> if r = r' then [] else [r, r']) (Array.to_list res2)) in
    { SortedRecords.columns = res.columns; neg_rows = Array.of_list (List.map (fun (a,b) -> b) res2); plus_rows = Array.of_list (List.map (fun (a,b) -> a) res2); }

let query_joined (lens : Value.t) (cols : string list) (data : SortedRecords.recs) =
    (* project data onto columns *)
    let proj = SortedRecords.project_onto data cols in
    (* for each record generate a phrase which matches join key *)
    let query_record row = Phrase.matching_cols_simp cols row in
    (* generate phrase as disjunction *)
    let query = List.fold_left Phrase.combine_or None (List.map (Phrase.matching_cols_simp cols) (Array.to_list proj.plus_rows)) in
    let to_join = lens_get_select_opt lens query in
    (* join to_join with data *)
    ()

let query_join_records (lens : Value.t) (set : SortedRecords.recs) (on : string list) =
    let proj = SortedRecords.project_onto set on in
    let recs = List.append (Array.to_list proj.plus_rows) (Array.to_list proj.neg_rows) in
    let recs = List.sort_uniq SortedRecords.compare recs in
    let query = List.fold_left Phrase.combine_or None (List.map (Phrase.matching_cols_simp on) recs) in
    let recs = lens_get_select_opt lens query in
    SortedRecords.construct_cols (lens_get_cols lens) recs

let rec lens_put_set_step (lens : Value.t) (delt : SortedRecords.recs) (fn : Value.t -> SortedRecords.recs -> unit) =
    match lens with
    | `Lens _ -> fn lens delt
    | `LensJoin (l1, l2, cols, pd, qd, sort)  -> 
            let cols_simp = List.map (fun (a,_,_) -> a) cols in
            let sort1 = get_lens_sort l1 in 
            let proj1 = SortedRecords.project_onto delt (get_lens_sort_cols_list sort1) in 
            let sort2 = get_lens_sort l2 in
            let proj2 = SortedRecords.project_onto delt (get_lens_sort_cols_list sort2) in
            let delta_m0 = get_changes l1 proj1 in
            let delta_n0 = get_changes l2 proj2 in
            let delta_l =
                SortedRecords.merge 
                    (SortedRecords.merge    
                        (SortedRecords.join delta_m0 delta_n0 cols_simp)
                        (SortedRecords.merge 
                            (SortedRecords.join delta_m0 (query_join_records l2 delta_m0 cols_simp) cols_simp)
                            (SortedRecords.join delta_n0 (query_join_records l1 delta_n0 cols_simp) cols_simp)
                        )
                    ) 
                    (SortedRecords.negate delt) in
            let j = SortedRecords.project_onto (SortedRecords.merge (query_join_records lens delta_l cols_simp) (delt)) cols_simp in
            let delta_l_l = SortedRecords.join delta_l j cols_simp in
            let delta_l_a = SortedRecords.merge (delta_l) (SortedRecords.negate delta_l_l) in
            let delta_m = SortedRecords.merge 
                (SortedRecords.merge delta_m0 (SortedRecords.negate (SortedRecords.project_onto_set (SortedRecords.filter delta_l_a pd) delta_m0)))
                (SortedRecords.negate (SortedRecords.project_onto_set delta_l_l delta_m0)) in
            let delta_n = SortedRecords.merge 
                delta_n0
                (SortedRecords.negate (SortedRecords.project_onto_set (SortedRecords.filter delta_l_a qd) delta_n0)) in
            fn l1 delta_m;
            fn l2 delta_n
            
    | `LensSelect (l, pred, sort) -> 
            let m_hash = delt in
            let delta_m1 = get_changes (lens_select l (Phrase.negate pred)) delt in
            let m1_cap_P = SortedRecords.filter delta_m1 pred in
            let delta_nhash = SortedRecords.merge (m1_cap_P) (SortedRecords.negate delt) in
            let new_delta = SortedRecords.merge delta_m1 (SortedRecords.negate delta_nhash) in
            fn l new_delta
    | _ -> failwith "Unsupport lens."

let lens_get_delta (lens : Value.t) (data : Value.t) =
    let cols = lens_get_cols lens in
    let orig = SortedRecords.construct_cols cols (lens_get lens ()) in
    let data = SortedRecords.merge (SortedRecords.construct_cols cols data) (SortedRecords.negate orig) in
    data


let lens_put_step (lens : Value.t) (data : Value.t) (fn : Value.t -> SortedRecords.recs -> unit) =
    let data = lens_get_delta lens data in
    lens_put_set_step lens data fn

let db_string_of_value (db : Value.database) (v : Value.t) =
    match v with
    | `Int i -> string_of_int i
    | `String s -> "'" ^ db#escape_string s ^ "'"
    | `Float f -> string_of_float f
    | _ -> failwith ("db_string_of_value does not support " ^ string_of_value v)

let rec take (l : 'a list) (n : int) = 
    match n with 
    | 0 -> []
    | _ -> List.hd l :: take (List.tl l) (n - 1)

let rec skip (l : 'a list) (n : int) =
    match n with 
    | 0 -> l
    | _ -> skip (List.tl l) (n - 1)

let apply_delta (t : Value.table) (data : SortedRecords.recs) =
    let show_query = false in
    let (db, _), table, keys, _ = t in
    (* get the first key, otherwise return an empty key *)
    let key = match keys with [] -> data.columns | _ -> List.hd keys in
    let key_len = List.length key in
    let cols = data.columns in
    let cols = SortedRecords.reorder_cols cols key in
    let data = (SortedRecords.project_onto data cols) in
    let (insert_vals, update_vals) = List.partition (fun row ->
        let key_vals = take row key_len in
        let row = SortedRecords.find_mul data.neg_rows key_vals in
        match row with None -> true | Some _ -> false) (Array.to_list data.plus_rows) in
    let delete_vals = List.map (fun row ->
        let key_vals = take row key_len in
        let row = SortedRecords.find_mul data.plus_rows key_vals in
        match row with None -> [key_vals] | Some _ -> []) (Array.to_list data.neg_rows) in
    let delete_vals = List.flatten delete_vals in
    let delete_commands = List.map (fun del_key ->
        let cond (key, v) = (db#quote_field key) ^ " = " ^ db_string_of_value db v in
        let zipped = List.combine key del_key in
        let cond = List.fold_left (fun a b -> a ^ " AND " ^ cond b) (cond (List.hd zipped)) (List.tl zipped) in
        let cmd = "delete from " ^ table ^ " where " ^ cond in
        if show_query then print_endline cmd else (); 
        db#exec cmd; 
        cmd) delete_vals in
    let update_commands = List.map (fun row ->
        let key_vals = take row key_len in
        let cond (key, v) = (db#quote_field key) ^ " = " ^ db_string_of_value db v in
        let zipped = List.combine key key_vals in
        let where = List.fold_left (fun a b -> a ^ " AND " ^ cond b) (cond (List.hd zipped)) (List.tl zipped) in
        let upd = skip (List.combine cols row) key_len in
        let upd = List.fold_left (fun a b -> a ^ ", " ^ cond b) (cond (List.hd upd)) (List.tl upd) in
        let cmd = "update " ^ table ^ " set " ^ upd ^ " where " ^ where in
        if show_query then print_endline cmd else (); 
        db#exec cmd;
        cmd
    ) update_vals in
    let insert_vals = List.map (fun row -> 
        List.map (db_string_of_value db) row) insert_vals in
    if insert_vals <> [] then
        let insert_cmd = db#make_insert_query (table, cols, insert_vals) in
        if show_query then print_endline insert_cmd else (); 
        db#exec insert_cmd;
        ()
    else
        ()

let get_fds (fds : (string list * string list) list) : Types.fundepset =
    let fd_of (left, right) = ColSet.of_list left, ColSet.of_list right in
    FunDepSet.of_list (List.map fd_of fds)

let rec lens_put (lens : Value.t) (data : Value.t) =
    let rec do_step_rec lens delt =
        match lens with
        | `Lens (t,_) -> apply_delta t delt 
        | _ -> lens_put_set_step lens delt do_step_rec in
    do_step_rec lens (lens_get_delta lens data)


