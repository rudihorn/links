open LensSetOperations
open OUnit2
open Value

let test_data_1 = { SortedRecords.columns = ["a"; "b"; "str";]; plus_rows = Array.of_list [
        [box_bool true; box_int 5; box_string "abc"];
        [box_bool true; box_int 3; box_string "this"];
        [box_bool false; box_int 9; box_string "0123"];
    ]; neg_rows = Array.of_list [
        [box_bool false; box_int 10; box_string "0123"];
        [box_bool false; box_int 11; box_string "0123"];
    ]}

let test_data_2 = { SortedRecords.columns = ["a"; "b"; "str";]; plus_rows = Array.of_list [
        [box_bool true; box_int 5; box_string "abc"];
        [box_bool false; box_int 10; box_string "0123"];
    ]; neg_rows = Array.of_list [
        [box_bool false; box_int 9; box_string "0123"];
    ]}

let test_data_3 = { SortedRecords.columns = ["C"; "B"; "A";]; plus_rows = Array.of_list [
        [box_bool true; box_int 5; box_string "abc"];
        [box_bool true; box_int 3; box_string "this"];
        [box_bool false; box_int 9; box_string "0123"];
        [box_bool false; box_int 9; box_string "01234"];
    ]; neg_rows = Array.of_list [
        [box_bool false; box_int 10; box_string "0123"];
        [box_bool false; box_int 11; box_string "0123"];
    ]}

let test_construct_set test_ctx =
    let recs = test_data_1 in
    assert_equal recs.columns ["a"; "b"; "str"];
    assert_equal recs.plus_rows (Array.of_list [
        [box_bool false; box_int 9; box_string "0123"];
        [box_bool true; box_int 3; box_string "this"];
        [box_bool true; box_int 5; box_string "abc"];
    ];);
    ()

let test_merge test_ctx =
    let merge = SortedRecords.merge test_data_1 test_data_2 in
    let str = SortedRecords.to_string_tabular merge in
    print_endline str;
    ()


let test_minus test_ctx = 
    let set = box_list [
        box_record ["a", box_bool true; "b", box_int 5; "str", box_string "abc"];
        box_record ["a", box_bool true; "b", box_int 3; "str", box_string "this"];
        box_record ["a", box_bool false; "b", box_int 9; "str", box_string "0123"];
    ] in
    let recs1 = SortedRecords.construct set in
    let set2 = box_list [
        box_record ["str", box_string "abc"; "b", box_int 5; ];
        box_record ["str", box_string "0123"; "b", box_int 9; ];
    ] in
    let recs2 = SortedRecords.construct set2 in
    let res = SortedRecords.minus recs1 recs2 in
    let str = SortedRecords.to_string_tabular res in
    (* print_endline ("\n" ^ str); *)
    ()

let test_project test_ctx = 
    let set = box_list [
        box_record ["a", box_bool true; "b", box_int 5; "str", box_string "abc"];
        box_record ["a", box_bool true; "b", box_int 3; "str", box_string "this"];
        box_record ["a", box_bool false; "b", box_int 9; "str", box_string "0123"];
    ] in
    let recs = SortedRecords.construct set in
    (* the project onto should drop 'nonexistant' *)
    let recs = SortedRecords.project_onto recs ["str"; "b"; "nonexistant"] in
    (* let str = SortedRecords.to_string_tabular recs in
    print_endline ("\n" ^ str); *)
    assert_equal recs {columns = ["str"; "b"]; plus_rows = Array.of_list [
        [box_string "0123"; box_int 9];
        [box_string "abc"; box_int 5];
        [box_string "this"; box_int 3];
    ]; neg_rows = Array.of_list []; }

let test_compare test_ctx = 
    let set = box_list [
        box_record ["a", box_bool true; "b", box_int 5; "str", box_string "abc"];
        box_record ["a", box_bool true; "b", box_int 3; "str", box_string "this"];
        box_record ["a", box_bool false; "b", box_int 9; "str", box_string "0123"];
    ] in
    let recs = SortedRecords.construct set in
    let find = [box_bool true; box_int 3; box_string "this"] in
    let cmp i = (SortedRecords.compare (Array.get (recs.plus_rows) i) find) in
    assert ((cmp 1) = 0);
    assert ((cmp 0) < 0);
    assert ((cmp 2) > 0)


let test_find_set test_ctx =
    let set1 = box_list [
        box_record ["a", box_bool true; "b", box_int 5; "str", box_string "abc"];
        box_record ["a", box_bool true; "b", box_int 3; "str", box_string "this"];
        box_record ["a", box_bool false; "b", box_int 9; "str", box_string "0123"];
    ] in
    let set2 = box_list [
        box_record ["a", box_bool true; "b", box_int 3; "str", box_string "this"];
    ] in
    let set3 = box_list [
        box_record ["a", box_bool false; "b", box_int 9; "str", box_string "0123"];
    ] in
    let set4 = box_list [
    ] in
    let find = [box_bool true; box_int 3; box_string "this"] in
    let find2 = [box_bool true; box_int 5; box_string "abc"] in
    let find3 = [box_bool false; box_int 9; box_string "0123"] in
    let test set find = SortedRecords.find (SortedRecords.construct set) find in
    assert (test set1 find);
    assert (test set2 find);
    assert (not (test set3 find));
    assert (not (test set3 find));
    assert (test set1 find2);
    assert (test set1 find3);
    ()


let suite =
    "lens_set_operations">:::
        [
            "construct_set">:: test_construct_set;
            "compare">:: test_compare;
            "find_set">:: test_find_set;
            "project">:: test_project;
            "minus">:: test_minus;
            "merge">:: test_merge;
        ];;
