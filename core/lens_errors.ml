open Lens

(** Unpack the result or format and throw the error using the [die] function. *)
let unpack_type_lens_result ~die res =
  match res with
  | Result.Ok t -> t
  | Result.Error e -> (
      let open Type.Lens_error in
      match e with
      | UnboundColumns c ->
          die
            (Format.asprintf "The columns %a were not bound."
               Alias.Set.pp_pretty c)
      | FunDepNotTreeForm ->
          die "The functional dependencies are not in tree form." )
