open OUnit2
open LensHelpers
open LensHelpersCorrect
open LensQueryHelpers
open LensRecordHelpers
open LensSetOperations
open UnitTestsLensCommon
open Value

module Query = struct 
    let lookup (col : string) (r : Value.t) =
        let rec fndi l = 
            let c,_ = List.hd l in
            if c = col then 0 else 1 + fndi (List.tl l) in
        fndi (unbox_record r)

    let skip f a b = f a

    let set (col : string) (fn : Value.t -> Value.t -> Value.t) (r : Value.t) =
        let r' = unbox_record r in
        let r' = List.map (fun (c,a) -> if col = c then (c,fn r a) else (c,a)) r' in
        box_record r'

    let ifcol (col : string) (bcond : Value.t -> bool) (i : Value.t) (r : Value.t) (oth : Value.t) =
        let (_,v) = List.find (fun (c,_) -> c = col) (unbox_record r) in
        if bcond v then i else oth

    let band (fn1 : Value.t -> bool) (fn2 : Value.t -> bool) (v : Value.t) =
        (fn1 v) && (fn2 v)

    let gt (i : int) (v : Value.t) =
        (unbox_int v) > i

    let lt (i : int) (v : Value.t) =
        (unbox_int v) < i

    let map_records fn recs = 
        let recs = unbox_list recs in
        let recs = List.map fn recs in
        box_list recs
end

let test_select_lens_1 n test_ctx = 
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (n / 15); `Rand] n in
    let l2 = LensTestHelpers.select_lens l1 (Phrase.equal (Phrase.var "b") (Phrase.constant_int 5)) in
    let res = lens_get l2 None in
    let res = Query.map_records (Query.set "c" (Query.ifcol "a" (Query.band (Query.gt 60) (Query.lt 80)) (box_int 5))) (lens_get l2 None) in
    let _ = LensTestHelpers.print_verbose test_ctx (string_of_value res) in
    let res = LensHelpersCorrect.lens_put l2 res in
    let _ = LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res) in
    let _ = LensTestHelpers.drop_if_cleanup test_ctx db "t1" in
    ()

let test_select_lens_2 n test_ctx =
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (200); `RandTo (30)] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d" "b d" [`Seq; `RandTo (40)] 50 in 
    let l3 = LensTestHelpers.join_lens l1 l2 ["b"] in
    let l4 = LensTestHelpers.select_lens l3 (
        Phrase.equal (Phrase.var "c") (Phrase.constant_int 20)) in
    let res = Query.map_records (Query.set "d" (Query.ifcol "b" (Query.band (Query.gt 40) (Query.lt 80)) (box_int 5))) (lens_get l4 ()) in
    let res = LensHelpersCorrect.lens_put l4 res in
    LensTestHelpers.print_verbose test_ctx (string_of_value (lens_get l4 ())); 
    LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res);
    LensTestHelpers.drop_if_cleanup test_ctx db "t1";
    LensTestHelpers.drop_if_cleanup test_ctx db "t2";
    ()




let suite =
    "lens_primitives">:::
        [
            "select_1_0">:: test_select_lens_1 0;
            "select_1_50">:: test_select_lens_1 100;
            "select_2_500">:: test_select_lens_2 500;
        ];;


