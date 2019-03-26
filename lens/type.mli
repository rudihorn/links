type t = Lens of Sort.t [@@deriving show]

val sort : t -> Sort.t

val equal : t -> t -> bool

module Lens_error : sig
  type t = UnboundColumns of Alias.Set.t | FunDepNotTreeForm
end

val type_lens_fun_dep :
     fds:((string list * string list) list)
  -> columns:Column.List.t
  -> (t, Lens_error.t) result
