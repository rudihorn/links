open OUnit2

let suites = 
   "All" >::: [
       "Lenses" >::: [
            UnitTestsLensCommon.suite;
            UnitTestsLensFDHelpers.suite;
            UnitTestsJson.suite;
        ];
   ];;

let () =
   run_test_tt_main suites;;
