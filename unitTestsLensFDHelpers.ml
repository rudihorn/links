open Debug
open LensFDHelpers
open OUnit2
open Utility

let _ = Settings.set_value Debug.debugging_enabled true

let fd_set = [
    (["A"; "B"], ["C"; "D"]); 
    (["C"; "D"], ["E"]); 
    (["E"], ["F"; "G"])
];;

let set = IntSet.of_list [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10];;
let _ = Debug.print (string_of_bool (set.mem 6));;

let test1 test_ctx = 
    let outp = get_fd_transitive_closure ["A"; "B"] fd_set in
    let _ = Debug.print (debug_print_col_list outp) in
    assert_equal (get_fd_transitive_closure ["A"; "B"] fd_set) ["A"; "B"; "C"; "D"; "E"; "F"; "G"];;

let suite =
    "lens_fd_helpers">:::
    ["test1">:: test1];;

let () =
    run_test_tt_main suite;;