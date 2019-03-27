type t = Lens of Sort.t [@@deriving show]

val sort : t -> Sort.t

val equal : t -> t -> bool

module Lens_error : sig
  type t =
    | UnboundColumns of Alias.Set.t
        (** Error thrown when there are references to columns
            in functional dependencies which don't exist. *)
    | ProbablyCycle of Alias.Set.t
        (** Error thrown when the algorithm assumes that some columns have not been included because there is some cycle with them. *)
    | FunDepNotTreeForm of Alias.Set.t  (** Error thrown when *)
end

val type_lens_fun_dep :
     fds:(string list * string list) list
  -> columns:Column.List.t
  -> (t, Lens_error.t) result

module Drop_lens_error : sig
  type t = Sort.Drop_sort_error.t
end

val type_drop_lens :
     t
  -> drop:Alias.t list
  -> default:Phrase_type.t list
  -> key:Alias.Set.t
  -> (t, Drop_lens_error.t) result
