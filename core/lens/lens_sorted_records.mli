(** This module provides an efficient method of performing calculations on delta sets. This is done by storing
    the records in a sorted order and by keeping track of the columns of the whole set of records rather than in
    each record itself. *)

open Lens_utility

module Simple_record : sig
  type t = Value.t list

  val compare_val: Value.t -> Value.t -> int

  val compare :  t -> t -> int

  (** Find to find the index of [record] in an array of records. *)
  val find_index : t array -> record:t -> int option

  (** Find the actual record in an array of records which partially matches on [record]. *)
  val find_record : t array -> record:t -> t option

  (** Find the index range of records matching [record]. *)
  val find_all_index : t array -> record:t -> int * int

  (** Get the array subset of records matching [record]. *)
  val find_all_record : t array -> record:t -> t array

  val equal : t -> t -> bool
end

module Inconsistent_columns_error : sig
  exception E of string list * string list
end

type t

val construct : records:Value.t -> t

val construct_cols : columns:string list -> records:Value.t -> t

val construct_full : columns:string list -> plus:Simple_record.t list -> neg:Simple_record.t list -> t

val columns : t -> string list

val plus_rows : t -> Simple_record.t array

val neg_rows : t -> Simple_record.t array

(** The record set does not contain negative entries. *)
val is_positive : t -> bool

(** The total number of records in the set. *)
val total_size : t -> int

val pp : t Format.fmt_fn

(** Print the set in tabular form. *)
val pp_tabular : t Format.fmt_fn

(** Returns true if the record set contains [record] as a positive row. *)
val find : t -> record:Simple_record.t -> bool

(** Generate a function which maps a set of columns to a subset of those columns
    specified by [columns].

    Example:

    {[
      let sr = (* sorted records with columns A, B, C, D *) in
      let map = get_cols_map sr ~columns:["B"; "D"] in
      let proj = map [1; 2; 3; 4] in
      (* proj = [2; 4] *)
    ]} *)
val get_cols_map : t -> columns:string list -> 'a list -> 'a list

val sort : t -> unit

(** Project the record set onto the given list of column names. *)
val project_onto : t -> columns:string list -> t

(** Project the record set onto the columns of [onto]. *)
val project_onto_set : t -> onto:t -> t

(** Filter out all records that don't match predicate. *)
val filter : t -> predicate:Lens_phrase.t -> t

(** Perform a delta merge (\oplus) between two record sets. *)
val merge : t -> t -> t

(** Reorder the columns, so that the columns [first] appear at the beginning. *)
val reorder : t -> first:string list -> t

(** Perform a relational join on two sets. [on] consists out of tuples with the order:
    - output name
    - left input name
    - right input name *)
val join : t -> t -> on:(string * string * string) list -> t

(** Swap positive and negative entries. *)
val negate : t -> t

(** Get only the negative subset of the record set. *)
val negative : t -> t

(** Subtract one delta set from another. Both sets must be positive only. *)
val minus : t -> t -> t

(** Convert a positive delta set into a value type. *)
val to_value : t -> Value.t

val project_fun_dep :
  t
  -> fun_dep:Lens_fun_dep.t
  -> (string list * string list) * (Simple_record.t * Simple_record.t) array * (Simple_record.t * Simple_record.t) array

val calculate_fd_changelist :
  t
  -> fun_deps:Lens_fun_dep.Set.t
  -> ((string list * string list) * (Simple_record.t * Simple_record.t) list) list

val relational_update :
  t
  -> fun_deps:Lens_fun_dep.Set.t
  -> update_with:t
  -> t

val relational_merge :
  t
  -> fun_deps:Lens_fun_dep.Set.t
  -> update_with:t
  -> t

(** Extend the given set of sorted records by the column [by] and populate it using
    the relational data [data] containing the functional dependency [key] -> [by].
    Use the default value specified if no entry in [data] is found. *)
val relational_extend :
  t
  -> key:string
  -> by:string
  -> data:t
  -> default:Value.t
  -> t

(** Get all distinct values of both positive and negative records in this set in a sorted list. *)
val all_values : t -> Simple_record.t list

val to_diff :
  t
  -> key:string list
  -> string list * (Simple_record.t list * Simple_record.t list * Simple_record.t list)
