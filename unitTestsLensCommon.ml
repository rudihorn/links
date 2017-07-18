
open Debug
open LensFDHelpers
open LensHelpers
open OUnit2
open Types
open Value
open Utility

module LensTestHelpers = struct
    let colslist_of_string str =
        let cols = String.split_on_char ' ' str in
        let cols = List.filter (fun s -> String.length s <> 0) cols in
        cols

    let rec_constr_int (cols : string) (vals : int list) =
        let cols = colslist_of_string cols in
        Value.box_record (List.map2 (fun c v -> (c, box_int v)) cols vals)

    let delt_constr_int (cols : string) (vals, m : int list * int) =
    rec_constr_int cols vals, m

    let colset_of_string str = 
        let cols = colslist_of_string str in
        ColSet.of_list cols

    let fundep_of_string str =
        let split = Str.split (Str.regexp "->") str in
        let _ = assert_equal (List.length split) 2 in
        let colsets = List.map colset_of_string split in
        FunDep.make (List.nth colsets 0) (List.nth colsets 1)

    let fundepset_of_string str =
        let split = Str.split (Str.regexp ";") str in
        let fds = List.map fundep_of_string split in
        FunDepSet.of_list fds

    let mem_lens (fd_set : fundepset) (name : string) data =
        let cols = FunDepSet.fold (fun fd fld -> ColSet.union_all [FunDep.left fd; FunDep.right fd; fld]) fd_set ColSet.empty in
        let cols = ColSet.elements cols in
        let colFn tbl name = {
            alias = name; name = name; table = tbl; typ = `Primitive `Int; present = true
        } in
        let l1 = `LensMem ((`List data), (fd_set, None, List.map (colFn name) cols)) in
        l1

    let mem_lens_str fds name data =
        mem_lens (fundepset_of_string fds) name data

    let join_lens l1 l2 on =
        let sort, on = join_lens_sort (get_lens_sort l1) (get_lens_sort l2) on in
        `LensJoin (l1, l2, on, sort)

    let select_lens l predicate =
        lens_get_select l predicate

end

let test_fundep_of_string test_ctx = 
    let fds = LensTestHelpers.fundepset_of_string "A B -> C; C -> D; D -> E F" in
    let _ = assert_equal "{{\"A\"; \"B\"; } -> {\"C\"; }; {\"C\"; } -> {\"D\"; }; {\"D\"; } -> {\"E\"; \"F\"; }; }" in
    ()


let suite =
    "lens_common_helpers">:::
    [
        "fundep_of_string">:: test_fundep_of_string;
    ];;
