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

let rec_constr a b c = Value.box_record ["A", box_int a; "B", box_int b; "C", box_int c]
let dat_update_recs = [rec_constr 1 2 3, -1; rec_constr 1 3 2, +1; rec_constr 2 1 3, -1; rec_constr 2 1 4, +1; rec_constr 3 4 5, 0; rec_constr 4 5 6, 1; rec_constr 5 6 7, -1]

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

let suite =
    "lens_fd_helpers">:::
    [
        "show_fd_set">:: test_show_fd_set;
        "transitive_closure">:: test_transitive_closure;
        "find_update_recs">:: test_find_update_recs;
        "is_update_record">:: test_is_update_record;
    ];;

let () =
    run_test_tt_main suite;;