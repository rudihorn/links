(*pp deriving *)

open Debug
open Json
open OUnit2
open Types
open Value
open Utility

(* let _ = Settings.set_value Debug.debugging_enabled true *)


let test_jsonize_value_list_empty test_ctx = 
   assert_equal "[]" (jsonize_value (`List []))

let test_jsonize_value_list_int test_ctx = 
   assert_equal "[5]" (jsonize_value (`List [`Int 5]))

let test_json_node_simple test_ctx =
   let res = json_node [
      ("test", `String, "hello");
      ("another", `Unquoted, string_of_bool true)
   ] in
   assert_equal "{test: \"hello\", another: true}" res 

let data_fds = FunDepSet.of_lists [(["A"; "B"],["C"; "D"]); (["E"], ["D"; "F"])]

let test_jsonize_sort_fds test_ctx =
   let res = jsonize_sort (data_fds, None, []) in
   assert_equal "{fds: [[[\"A\", \"B\"], [\"C\", \"D\"]], [[\"E\"], [\"D\", \"F\"]]], cols: []}" res

let data_phrase = `InfixAppl (`Name "+", `Constant (`Int 5), `Var "test")

let test_jsonize_sort_phrase test_ctx = 
   let sort = (FunDepSet.empty, Some data_phrase, []) in
   let res = jsonize_sort sort in
   assert_equal "{fds: [], phrase: {infx: \"+\", l: 5, r: {var: \"test\"}}, cols: []}" res

let data_cols = [{
   table = "items";
   name = "title";
   alias = "title_1";
   typ = `Primitive `Bool;
   present = true
};{
   table = "items2";
   name = "title2";
   alias = "title_3";
   typ = `Primitive `Int;
   present = true
}]

let test_jsonize_sort_cols test_ctx =
   let sort = (FunDepSet.empty, None, data_cols) in
   let res = jsonize_sort sort in
   assert_equal "{fds: [], cols: [{table: \"items\", name: \"title\", alias: \"title_1\", typ: \"Bool\", present: true}, {table: \"items2\", name: \"title2\", alias: \"title_3\", typ: \"Int\", present: true}]}" res

let data_db = new LensQueryHelpers.dummy_database, "db:localhost:5432:usr:pwd" 

let data_rec_cols = match LensRecordHelpers.get_record_type_from_cols data_cols with
| `Record r -> r

let data_table = data_db, "mytable", [], data_rec_cols

let data_lens = `Lens (data_table, (data_fds, Some data_phrase, data_cols))


let test_jsonize_value_lens test_ctx =
   let res = jsonize_value data_lens in
   (* let _ = Debug.print res in *)
   assert_equal "{_lens: {_table:{db:'{_db:{driver:\"dummy\",name:\"db\", args:\"localhost:5432:usr:pwd\"}}',name:\"mytable\",row:\"(title_1:Bool,title_3:Int)\",keys:\"[]\"}}, _sort: {fds: [[[\"A\", \"B\"], [\"C\", \"D\"]], [[\"E\"], [\"D\", \"F\"]]], phrase: {infx: \"+\", l: 5, r: {var: \"test\"}}, cols: [{table: \"items\", name: \"title\", alias: \"title_1\", typ: \"Bool\", present: true}, {table: \"items2\", name: \"title2\", alias: \"title_3\", typ: \"Int\", present: true}]}}" res

let test_parse_json_phrase test_ctx = 
   let sort = (FunDepSet.empty, Some data_phrase, []) in
   let res = jsonize_sort sort in
   (* let _ = Debug.print res in *)
   let phrase = Json.parse_json res in
   let phrase = Jsonparsehelpers.parse_json_sort phrase in
   assert_equal sort phrase 

let test_parse_json_lens test_ctx =
   let res = Json.jsonize_value data_lens in
   let lens = Json.parse_json res in
   assert_equal data_lens lens

let suite =
   "json" >:::
      [
         "json_node" >::: [
            "simple" >:: test_json_node_simple;
         ];
         "jsonize_sort" >::: [
            "fds" >:: test_jsonize_sort_fds;
            "phrase" >:: test_jsonize_sort_phrase;
            "cols" >:: test_jsonize_sort_cols;
         ];
         "jsonize_value" >::: [
            "list_empty" >:: test_jsonize_value_list_empty;
            "list_int" >:: test_jsonize_value_list_int;
            "lens" >:: test_jsonize_value_lens;
         ];
         "parse_json" >::: [
            "phrase" >:: test_parse_json_phrase;
            (* "lens" >:: test_parse_json_lens; *)
         ];
      ];;

