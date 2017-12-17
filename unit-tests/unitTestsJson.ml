(*pp deriving *)

open Debug
open Json
open OUnit2
open Types
open Value
open Utility
open TestHelpers

let test_jsonize_value_list_empty test_ctx = 
    let result = jsonize_value (box_list []) in
    Helpers.print test_ctx result;
    assert_equal "null" result

let test_jsonize_value_list_int test_ctx = 
    let result = jsonize_value (box_list [box_int 5]) in
    Helpers.print test_ctx result;
    assert_equal "{\"_head\":5, \"_tail\":null}" result

let suite =
   "json" >:::
      [
         "jsonize_value" >::: [
            "list_empty" >:: test_jsonize_value_list_empty;
            "list_int" >:: test_jsonize_value_list_int;
         ];
      ];;

