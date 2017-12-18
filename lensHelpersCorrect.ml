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
    let res = match phrase with
    | None -> lens_get lens ()
    | Some phrase -> lens_get_select lens phrase in
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


let rec lens_put_set (lens : Value.t) (set : SortedRecords.recs) =
    (* first step is calculate the delta *)
    let res = LensHelpers.lens_get lens () in
    let delt = SortedRecords.merge set (SortedRecords.negate (SortedRecords.construct_cols set.columns res)) in
    (* now perform lens step *)
    match lens with
    | `Lens _ -> set 
    | `LensSelect (l, pred, sort) -> 
            let m_hash = set in
            let delta_m1 = get_changes (lens_select l (Phrase.negate pred)) delt in
            
            let m1_cap_P = SortedRecords.filter delta_m1 pred in
            let delta_nhash = SortedRecords.merge (m1_cap_P) (SortedRecords.negate set) in
            SortedRecords.merge delta_m1 (SortedRecords.negate delta_nhash)
    | _ -> failwith "Unsupport lens."

let rec lens_put (lens : Value.t) (data : Value.t) =
    let cols = lens_get_cols lens in
            print_endline (string_of_value (box_list (List.map box_string cols)));
    let orig = SortedRecords.construct_cols cols (lens_get lens ()) in
    let data = SortedRecords.merge (SortedRecords.construct_cols cols data) (SortedRecords.negate orig) in
    lens_put_set lens data


