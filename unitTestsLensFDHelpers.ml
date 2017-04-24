(*pp deriving *)

open Debug
open LensFDHelpers
open OUnit2
open Types
open Value
open Utility

let _ = Settings.set_value Debug.debugging_enabled true

(* data *)

let dat_fd_set_l = [
    (["A"; "B"], ["C"; "D"]); 
    (["C"; "D"], ["E"]); 
    (["E"], ["F"; "G"])
]
let dat_fd_set = FunDepSet.of_lists dat_fd_set_l

let dat_cols_l = ["C"; "D"; ]
let dat_cols = ColSet.of_list dat_cols_l

let dat_closure_l = ["C"; "D"; "E"; "F"; "G"]
let dat_closure = ColSet.of_list dat_closure_l

let dat_fd_set_2_l = [
    (["A"], ["B"]);
    (["B"], ["C"])
]
let dat_fd_set_2 = FunDepSet.of_lists dat_fd_set_2_l

let rec_constr (cols : string list) (vals : int list) = Value.box_record (List.map2 (fun c v -> (c, box_int v)) cols vals)
let delt_constr (cols : string list) (vals, m : int list * int) = rec_constr cols vals, m
let dat_update_recs = List.map (delt_constr ["A"; "B"; "C"]) [[1; 2; 3], -1; [1; 3; 2], +1; [2; 1; 3], -1; [2; 1; 4], +1; [3; 4; 5], 0; [4; 5; 6], 1; [5; 6; 7], -1]


(* Tests *)

let test_show_fd_set test_ctx = 
    let show = FunDepSet.Show_t.show dat_fd_set in
    (* let _ = Debug.print show in *)
    let cmp = "{{\"A\"; \"B\"; } -> {\"C\"; \"D\"; }; {\"C\"; \"D\"; } -> {\"E\"; }; {\"E\"; } -> {\"F\"; \"G\"; };}" in
    ()
    (* assert_equal show cmp *)

let test_transitive_closure test_ctx = 
    let outp = get_fd_transitive_closure dat_cols dat_fd_set in
    assert_equal true (ColSet.equal outp dat_closure)

let test_find_update_recs test_ctx =
    let matches fd ind1 ind2 =
        let res = find_update_record fd (List.nth dat_update_recs ind1) dat_update_recs in
        match res with
        | None -> assert_failure "Should find complementary record."
        | Some r -> assert_equal (List.nth dat_update_recs ind2) r in
    let fd = FunDepSet.min_elt dat_fd_set_2 in
    let _ = matches fd 0 1 in
    let fd = FunDepSet.max_elt dat_fd_set_2 in
    matches fd 2 3

let test_is_update_record test_ctx =
    let res = List.map (fun a -> is_update_record dat_fd_set_2 a dat_update_recs) dat_update_recs in
    assert_equal [true; true; true; true; false; false; false] res

let test_join_update_filter test_ctx =
    let dat_fd_set_1 = FunDepSet.of_lists [
        (["A"], ["B"]);
        (["B"], ["C"])
    ] in
    let dat_fd_set_2 = FunDepSet.of_lists [
        (["B"], ["D"]);
        (["D"], ["E"])
    ] in
    let rec_constr m a b c d e = Value.box_record ["A", box_int a; "B", box_int b; "C", box_int c; "D", box_int d; "E", box_int e], m in
    let data = [
        rec_constr (-1) 1 1 1 1 1;
        rec_constr 1 1 2 1 1 1;
        rec_constr 1 1 1 3 1 1;
        rec_constr (-1) 2 3 2 2 2;
        rec_constr 1 2 3 2 3 3;
        rec_constr 1 4 4 4 4 4;
    ] in
    let nth n = List.nth data n in
    let cmp = [], [nth 0; nth 1; nth 2], [nth 3; nth 4], [nth 5] in
    assert_equal cmp (lens_join_split_updates dat_fd_set_1 dat_fd_set_2 data)

let construct_join_lens (fd_set : fundepset) (name : string) data =
    let cols = FunDepSet.fold (fun fd fld -> ColSet.union_all [FunDep.left fd; FunDep.right fd; fld]) fd_set ColSet.empty in
    let cols = ColSet.elements cols in
    let colFn tbl name = {
        alias = name; name = name; table = tbl; typ = `Primitive `Int; present = true
    } in
    let l1 = `LensMem ((`List data), (fd_set, None, List.map (colFn "table1") cols)) in
    l1

let run_join_test_case_1 data exp1 exp2 dbg =
    let dat_fd_set_1 = FunDepSet.of_lists [
        (["A"], ["B"]);
        (["B"], ["C"])
    ] in
    let dat_fd_set_2 = FunDepSet.of_lists [
        (["B"], ["D"]);
        (["D"], ["E"])
    ] in
    let on = ["B", "table1", "B"] in
    let l1 = construct_join_lens dat_fd_set_1 "table1" [] in
    let l2 = construct_join_lens dat_fd_set_2 "table2" [] in
    let constr_cmp_left data = List.map (delt_constr ["A"; "B"; "C"]) data in
    let constr_cmp_right data = List.map (delt_constr ["B"; "D"; "E"]) data in
    let constr_data = List.map (delt_constr ["A"; "B"; "C"; "D"; "E"]) in
    let (outp1, outp2) = LensHelpers.lens_delta_put_join l1 l2 on (constr_data data) in
    let _ = if dbg then
        let _ = LensHelpers.lens_debug_delta outp1 in
        let _ = LensHelpers.lens_debug_delta outp2 in
        ()
    else
        () in
    let _ = assert_equal outp1 (constr_cmp_left exp1) in
    let _ = assert_equal outp2 (constr_cmp_right exp2) in
    ()

let test_join_1_insert_new test_ctx = 
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], +1
    ] [
        [1; 1; 1], 1
    ] [
        [1; 1; 1], 1
    ] false

let test_join_1_update_right test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], +1;
        [1; 1; 1; 2; 1], -1
    ] [
    ] [
        [1; 1; 1], 1;
        [1; 2; 1], -1
    ] false

let test_join_1_left_remove_left_add test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], -1;
        [2; 1; 1; 1; 1], +1
    ] [
        [1; 1; 1], -1;
        [2; 1; 1], +1
    ] [
    ] false

let test_join_1_left_remove_left_add_2 test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], -1;
        [1; 2; 1; 1; 1], +1
    ] [
        [1; 1; 1], -1;
        [1; 2; 1], +1
    ] [
        [2; 1; 1], +1
    ] false

let test_join_1_left_update test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], -1;
        [1; 1; 2; 1; 1], +1
    ] [
        [1; 1; 1], -1;
        [1; 1; 2], +1
    ] [
    ] false


let test_join_1_weird_fd_right_change test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], -1;
        [1; 2; 1; 2; 1], +1
    ] [
        [1; 1; 1], -1;
        [1; 2; 1], +1
    ] [
        [2; 2; 1], +1
    ] false

let test_join_side_effects test_ctx =
    run_join_test_case_1 [
        [1; 1; 1; 1; 1], -1;
        [1; 1; 2; 1; 1], +1;
        [2; 1; 2; 1; 1], 0
    ] [
        [1; 1; 1], -1;
        [1; 2; 1], +1
    ] [
        [2; 2; 1], +1
    ] false


let suite =
    "lens_fd_helpers">:::
    [
        "show_fd_set">:: test_show_fd_set;
        "transitive_closure">:: test_transitive_closure;
        "find_update_recs">:: test_find_update_recs;
        "is_update_record">:: test_is_update_record;
        "join_update_filter">:: test_join_update_filter;
        "join_1_insert_new">:: test_join_1_insert_new;
        "join_1_update_right">:: test_join_1_update_right;
        "join_1_left_remove_left_add">:: test_join_1_left_remove_left_add;
        "join_1_left_remove_left_add_2">:: test_join_1_left_remove_left_add_2;
        "join_1_left_update">:: test_join_1_left_update;
        "join_1_weird_fd_right_change">::test_join_1_weird_fd_right_change;

    ];;

let () =
    run_test_tt_main suite;;