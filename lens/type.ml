open Lens_utility

type t = Lens of Sort.t

let pp f _ = Format.fprintf f "Lens"

let show _ = "Lens"

let sort v = match v with Lens sort -> sort

let equal t1 t2 =
  match (t1, t2) with Lens sort1, Lens sort2 -> Sort.equal sort1 sort2

module Lens_error = struct
  type t =
    | UnboundColumns of Alias.Set.t
        (** Error thrown when there are references to columns
            in functional dependencies which don't exist. *)
    | FunDepNotTreeForm
        (** Error thrown when a tree form of the functional
            dependencies cannot be constructed or when it is invalid. *)

  let of_fun_dep_check_error e =
    match e with Fun_dep.Check_error.UnboundColumns c -> UnboundColumns c
end

let check_tree_form fds ~columns =
  let tree = Fun_dep.Tree.of_fds fds ~columns in
  if Fun_dep.Tree.is_disjoint tree ~columns then Result.return ()
  else Result.error Lens_error.FunDepNotTreeForm

let type_lens_fun_dep ~fds ~columns =
  let cols = columns in
  let columns = Column.List.present_aliases_set columns in
  let open Result.O in
  Fun_dep.Set.checked_fds_of_lists fds ~columns
  |> Result.map_error ~f:Lens_error.of_fun_dep_check_error
  >>= fun fds ->
  check_tree_form fds ~columns
  >>| fun () ->
  let sort = Sort.make ~fds cols in
  Lens sort
