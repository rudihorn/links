open OUnit2
open LensHelpers
open LensQueryHelpers
open LensRecordHelpers
open UnitTestsLensCommon
open Value

let performance_opt = Conf.make_bool "performance" false "Run performance tests."

let skip_performance test_ctx =
    let v = performance_opt test_ctx in
    skip_if (not v) "Not running performance tests"

let test_join_five test_ctx n = 
    skip_performance test_ctx;
    let db = LensTestHelpers.get_db test_ctx in
    let l1 = LensTestHelpers.drop_create_populate_table test_ctx db "t1" "a -> b c" "a b c" [`Seq; `RandTo (n / 15); `Rand] n in
    let l2 = LensTestHelpers.drop_create_populate_table test_ctx db "t2" "b -> d e" "b d e" [`Seq; `RandTo (n / 15 / 15); `Rand] (n / 15) in
    let l3 = LensTestHelpers.drop_create_populate_table test_ctx db "t3" "d -> f g" "d f g" [`Seq; `RandTo (n / 15 / 15 / 15); `Rand] (n / 15 / 15) in
    let l4 = LensTestHelpers.drop_create_populate_table test_ctx db "t4" "f -> h" "f h" [`Seq; `Rand] (n / 15 / 15 / 15) in
    let l5 = LensTestHelpers.join_lens l1 l2 ["b"] in
    let l6 = LensTestHelpers.join_lens l3 l4 ["f"] in
    let l7 = LensTestHelpers.join_lens l5 l6 ["d"] in
    let l8 = LensTestHelpers.select_lens l7 (Phrase.equal (Phrase.var "b") (Phrase.constant_int 10)) in
    (* run tests *)
    let res = lens_get l8 None in
    let r = LensTestHelpers.time_query_both (fun () -> lens_put l8 res None) in
    let _ = LensTestHelpers.print_verbose test_ctx (string_of_value res) in
    (* modify res *)
    let res = unbox_list res in
    let row = List.hd res in
    let row = Record.set_column row "a" (box_int (n + 1)) in
    let res = box_list (row :: res) in
    let r = LensTestHelpers.time_query_both (fun () -> lens_put l8 res None) in
    let _ = LensTestHelpers.print_verbose test_ctx (string_of_value res) in
    let _ = LensTestHelpers.drop_if_cleanup test_ctx db "t1" in
    let _ = LensTestHelpers.drop_if_cleanup test_ctx db "t2" in
    let _ = LensTestHelpers.drop_if_cleanup test_ctx db "t3" in
    let _ = LensTestHelpers.drop_if_cleanup test_ctx db "t4" in
    ()

let test_join_five_10000 test_ctx = 
    test_join_five test_ctx 10000

let suite = 
    "lens_performance">:::
        [
            "join_five_10000">:: test_join_five_10000;
        ];;
