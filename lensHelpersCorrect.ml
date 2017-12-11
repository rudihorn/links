open Types
open LensQueryHelpers
open LensFDHelpers
open LensSetOperations

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
    res

let matches_change changes = 
    let is_changed_row (r : Value.t) =

    let is_changed ((cols_l, cols_r),(vals_l, vals_r)) =
        List.map (fun vals -> is_changed_row (SortedRecords.box_simp_rec cols_l vals)) vals_l

    ()

let rec lens_put_set (lens : Value.t) (set : SortedRecords.recs) =
    match lens with
    | `Lens _ -> set
    | `LensSelect (l, pred, sort) -> 
            let m_hash = set in
            m_hash
    | _ -> failwith "Unsupport lens."

let rec lens_put (lens : Value.t) (data : Value.t) =
    lens_put_set lens (SortedRecords.construct data)


