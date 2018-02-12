open OUnit2
open LensHelpers
open LensHelpersCorrect
open LensQueryHelpers
open LensRecordHelpers
open LensSetOperations
open UnitTestsLensCommon
open Value

(* define composition operator *)
let (<<) f g x = f (g x)

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

    let col (col : string) (v : Value.t) = 
        let (_,v) = List.find (fun (c,_) -> c = col) (unbox_record v) in
        v

    let map_records fn recs = 
        let recs = unbox_list recs in
        let recs = List.map fn recs in
        box_list recs

    let filter fn recs =
        let recs = unbox_list recs in
        let recs = List.filter fn recs in
        box_list recs

end

let _ = Settings.set_value Debug.debugging_enabled true  


let test_put test_ctx lens res =
    if UnitTestsLensCommon.classic_opt test_ctx then
        begin
            LensHelpersClassic.lens_put_step lens res (fun _ res ->
                LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res)
            );
            print_endline "begin";
            LensTestHelpers.time_query false (fun () -> LensHelpersClassic.lens_put lens res)
            ; print_endline "end"
        end
    else
        begin
            LensHelpersCorrect.lens_put_step lens res (fun _ res ->
                LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res)
            );
            print_endline "begin";
            LensTestHelpers.time_query false (fun () -> LensTestHelpers.print_query_time (); LensHelpersCorrect.lens_put lens res)
            ; print_endline "end"
        end;
    let upd = lens_get lens None in
    LensTestHelpers.print_verbose test_ctx (string_of_value upd);
    LensTestHelpers.print_verbose test_ctx (string_of_value res);
    LensTestHelpers.assert_rec_list_eq upd res;
    ()

let test_select_lens_1 n test_ctx = 
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (n / 15); `Rand] n in
    let l2 = LensTestHelpers.select_lens l1 (Phrase.equal (Phrase.var "b") (Phrase.constant_int 5)) in
    let res = lens_get l2 None in
    let res = Query.map_records (Query.set "c" (Query.ifcol "a" (Query.band (Query.gt 60) (Query.lt 80)) (box_int 5))) (lens_get l2 None) in
    test_put test_ctx l2 res;
    LensTestHelpers.drop_if_cleanup test_ctx db "t1"

let test_drop_lens_1 n test_ctx = 
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (n / 15); `Rand] n in
    let l2 = LensTestHelpers.drop_lens l1 "c" "a" (box_int 1) in
    let res = lens_get l2 None in
    let res = Query.map_records (Query.set "b" (Query.ifcol "a" (Query.band (Query.gt 60) (Query.lt 80)) (box_int 5))) (lens_get l2 None) in
    test_put test_ctx l2 res;
    LensTestHelpers.drop_if_cleanup test_ctx db "t1"

let test_select_lens_2 n test_ctx =
    let db = LensTestHelpers.get_db test_ctx in
    let upto = n / 10 in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (upto); `RandTo (100)] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d" "b d" [`Seq; `RandTo (upto)] upto in 
    let l3 = LensTestHelpers.join_lens_dl l1 l2 ["b"] in
    let l4 = LensTestHelpers.select_lens l3 (
        Phrase.equal (Phrase.var "c") (Phrase.constant_int 3)) in
    let res = Query.map_records (Query.set "d" (Query.ifcol "b" (Query.band (Query.gt 100) (Query.lt 200)) (box_int 5))) (lens_get l4 ()) in
    test_put test_ctx l4 res; 
    LensTestHelpers.drop_if_cleanup test_ctx db "t1";
    LensTestHelpers.drop_if_cleanup test_ctx db "t2";
    ()

let test_join_lens_1 n test_ctx =
    let db = LensTestHelpers.get_db test_ctx in
    let upto = n / 10 in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (upto); `RandTo (100)] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d" "b d" [`Seq; `RandTo (upto)] upto in 
    let l3 = LensTestHelpers.join_lens_dl l1 l2 ["b"] in
    let res = Query.map_records (Query.set "c" (Query.ifcol "b" (Query.band (Query.gt 40) (Query.lt 50)) (box_int 5))) (lens_get l3 ()) in
    test_put test_ctx l3 res;
    LensTestHelpers.drop_if_cleanup test_ctx db "t1";
    LensTestHelpers.drop_if_cleanup test_ctx db "t2";
    () (*
    assert (res.plus_rows = Array.of_list [
        [box_int 2; box_string "12"; box_string "data";];
        [box_int 3; box_string "this"; box_string "in";];
        [box_int 5; box_string "abc"; box_string "other";];
        [box_int 5; box_string "abc"; box_string "table";];
        [box_int 5; box_string "abc"; box_string "this";];
        [box_int 14; box_string "9012"; box_string "exists";]
    ]) *)

let test_join_lens_2 n test_ctx =
    let db = LensTestHelpers.get_db test_ctx in
    let upto = n / 10 in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (upto); `RandTo (30)] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d" "b d" [`Seq; `RandTo (40)] upto in 
    let l3 = LensTestHelpers.join_lens_dl l1 l2 ["b"] in
    let res = Query.filter (Query.lt 40 << Query.col "b") (lens_get l3 ()) in
    LensTestHelpers.print_verbose test_ctx (string_of_value (lens_get l3 ())); 
    LensTestHelpers.print_verbose test_ctx (string_of_value res);
    LensHelpersCorrect.lens_put_step l3 res (fun _ res ->
        LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res)
    );
    LensHelpersCorrect.lens_put l3 res; 
    let upd = lens_get l3 None in
    LensTestHelpers.print_verbose test_ctx (string_of_value upd);
    LensTestHelpers.print_verbose test_ctx (string_of_value res);
    LensTestHelpers.assert_rec_list_eq upd res; 
    LensTestHelpers.drop_if_cleanup test_ctx db "t1";
    LensTestHelpers.drop_if_cleanup test_ctx db "t2";
    () 

let test_join_lens_dr_2 n test_ctx =
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (200); `RandTo (30)] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d" "b d" [`Seq; `RandTo (40)] 50 in 
    let l3 = LensTestHelpers.join_lens_dr l1 l2 ["b"] in
    let res = Query.filter (Query.lt 20 << Query.col "c") (lens_get l3 ()) in
    LensTestHelpers.print_verbose test_ctx (string_of_value (lens_get l3 ())); 
    LensTestHelpers.print_verbose test_ctx (string_of_value res);
    LensHelpersCorrect.lens_put_step l3 res (fun _ res ->
        LensTestHelpers.print_verbose test_ctx (SortedRecords.to_string_tabular res)
    );
    LensHelpersCorrect.lens_put l3 res; 
    let upd = lens_get l3 None in
    LensTestHelpers.print_verbose test_ctx (string_of_value upd);
    LensTestHelpers.print_verbose test_ctx (string_of_value res);
    LensTestHelpers.assert_rec_list_eq upd res; 
    LensTestHelpers.drop_if_cleanup test_ctx db "t1";
    LensTestHelpers.drop_if_cleanup test_ctx db "t2";
    () 

let suite =
    "lens_primitives">:::
        [
            "select_1_0">:: test_select_lens_1 0;
            "select_1_50">:: test_select_lens_1 50;
            "select_2_500">:: test_select_lens_2 500;
            "select_2_10000">:: test_select_lens_2 10000;
            "drop_1_100">:: test_drop_lens_1 100;
            "join_1_100">:: test_join_lens_1 100;
            "join_1_10000">:: test_join_lens_1 10000;
            "join_2_100">:: test_join_lens_2 100;
            "join_2_dr_100">:: test_join_lens_dr_2 100;
        ];;


