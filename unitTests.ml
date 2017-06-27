open OUnit2

let suites = 
   "All" >::: [
      UnitTestsLensFDHelpers.suite;
      UnitTestsJson.suite
   ];;

let () =
   run_test_tt_main suites;;
