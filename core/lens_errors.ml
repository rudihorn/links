open Lens

(** Unpack the result or format and throw the error using the [die] function. *)
let unpack_type_lens_result ~die res =
  match res with
  | Result.Ok t -> t
  | Result.Error e -> (
      let open Type.Lens_error in
      match e with
      | UnboundColumns c ->
          Format.asprintf "The columns { %a } were not bound."
            Alias.Set.pp_pretty c
          |> die
      | FunDepNotTreeForm c ->
          Format.asprintf
            "The functional dependencies are not in tree form. There seems to \
             be an error with the columns { %a }."
            Alias.Set.pp_pretty c
          |> die
      | ProbablyCycle c ->
          Format.asprintf
            "There is possibly a cycle or non-disjoint references with \
             functional dependencies involving { %a }."
            Alias.Set.pp_pretty c
          |> die )

let format_drop_sort_error e =
  let open Sort.Drop_sort_error in
  match e with
  | UnboundColumns c ->
      Format.asprintf "The columns { %a } are not bound by the lens."
        Alias.Set.pp_pretty c
  | DropNotDefinedByKey ->
      Format.asprintf
        "The functional dependencies do not specify that the drop columns are \
         defined by the key columns."
  | DefaultDropMismatch ->
      Format.asprintf
        "The number of default values does not match the number of drop \
         columns."
  | DropTypeError {column; default_type; column_type} ->
      Format.asprintf
        "The type of column '%s' is %a, but the default value is of type %a."
        column Phrase.Type.pp column_type Phrase.Type.pp default_type

let unpack_type_drop_lens_result ~die res =
  match res with
  | Result.Ok t -> t
  | Result.Error e -> format_drop_sort_error e |> die
