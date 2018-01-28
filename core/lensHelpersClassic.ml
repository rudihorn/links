open Types
open Value
open Utility
open LensQueryHelpers
open LensHelpers
open LensHelpersCorrect
open LensFDHelpers
open LensSetOperations
open LensRecordHelpers



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
            let nh = SortedRecords.minus (SortedRecords.filter m1 pred) data in
            let r = SortedRecords.minus m1 nh in 
            fn lens r
    | _ -> ()

