open Types
open Value
open Utility
open LensQueryHelpers
open LensHelpers
open LensHelpersCorrect
open LensFDHelpers
open LensSetOperations
open LensRecordHelpers



let relational_update (fds : Types.fundepset) (changedata : SortedRecords.recs) (updatedata : SortedRecords.recs) =
    let fds = fds in
    let changelist = calculate_fd_changelist fds changedata in
    let changes = List.map (fun ((cols_l,cols_r),l) -> 
        (* get a map from simp rec to col value *)
        let col_maps = List.map (SortedRecords.get_col_map updatedata) cols_l in
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
    (* each entry in changelist is a functional dependency, and then the corresponding records *)
    (* generate a function for every change list entry, which can replace the columns in the
     * right side of the functional dependency of a record in res *)
    let apply_changes = List.map (fun ((cols_l, cols_r),l) ->
        (* upd cols returns a function which, given a record another record containing cols_r,
         * replaces every column value in the first record from that in the second record if it 
         * matches *)
        let rec upd cols =
            match cols with 
            | [] -> fun r target -> []
            | x :: xs -> 
                let fn = upd xs in
                (* get a function which maps a row to the x's value *)
                let map = SortedRecords.get_col_map_list cols_r x in
                match map with 
                | None -> (* the column does not have to be replaced *)
                        fun (y :: ys) target -> y :: fn ys target 
                | Some mp -> (* the column has been found, replace *)
                        fun (y :: ys) target -> 
                            mp target :: fn ys target
                in 
        upd updatedata.columns 
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
    let res2 = update updatedata.plus_rows in
    let res = { SortedRecords.columns = updatedata.columns; neg_rows = Array.of_list []; plus_rows = Array.map (fun (a,b) -> a) res2; } in
    SortedRecords.sort_uniq res

let rec lens_put_set_step (lens : Value.t) (data : SortedRecords.recs) (fn : Value.t -> SortedRecords.recs -> unit) =
    let get l = 
        let dat = LensHelpers.lens_get l () in
        SortedRecords.construct_cols (lens_get_cols l) dat in
    match lens with
    | `Lens _ -> fn lens data
    | `LensDrop (l, drop, key, default, sort) -> 
            let old = LensHelpers.lens_get l () in
            fn lens data
    | `LensJoin (l1, l2, cols, pd, qd, sort)  -> 
            let old = LensHelpers.lens_get l1 () in
            let old = LensHelpers.lens_get l2 () in
            fn lens data
    | `LensSelect (l, pred, sort) ->
            let sort = get_lens_sort l in
            let r = get l in
            let m1 = relational_update (LensSort.fundeps sort) data (SortedRecords.filter r pred) in
            print_endline (SortedRecords.to_string_tabular data);
            print_endline (SortedRecords.to_string_tabular m1);
            let nh = SortedRecords.minus (SortedRecords.filter m1 pred) data in
            let r = SortedRecords.minus m1 nh in 
            fn l r
    | _ -> ()

let apply_table_data (t : Value.table) (data : SortedRecords.recs) =
    let show_query = false in
    let (db, _), table, keys, _ = t in
    let cmd = "delete from " ^ db#quote_field table ^ " where TRUE" in
    db#exec cmd;
    if show_query then print_endline cmd else ();
    let cols = data.columns in
    let insert_vals = List.map (fun row -> 
        List.map (db_string_of_value db) row) (Array.to_list data.plus_rows) in
    if insert_vals <> [] then
        begin
            let insert_cmd = db#make_insert_query (table, cols, insert_vals) in
            if show_query then print_endline insert_cmd else (); 
            db#exec insert_cmd;
            ()
        end;
    ()

let lens_put_step (lens : Value.t) (data : Value.t) (fn : Value.t -> SortedRecords.recs -> unit) =
    let data = SortedRecords.construct_cols (lens_get_cols lens) data in
    lens_put_set_step lens data fn

let rec lens_put (lens : Value.t) (data : Value.t) =
    let rec do_step_rec lens data =
        match lens with
        | `Lens (t,_) -> apply_table_data t data 
        | _ -> lens_put_set_step lens data do_step_rec in
    do_step_rec lens (SortedRecords.construct_cols (lens_get_cols lens) data)


