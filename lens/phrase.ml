open Operators
open Lens_utility
module Value = Phrase_value

type t =
  | Constant of Value.t
  | Var of Alias.t
  | InfixAppl of Operators.Binary.t * t * t
  | UnaryAppl of Operators.Unary.t * t
  (* the In operator checks if the tuple generated by the names list is
   * in the list of constant tuples *)
  | In of string list * Value.t list list
  | Case of t option * (t * t) list * t
  | TupleLit of t list
[@@deriving show]

let var n = Var n

let infix op v1 v2 = InfixAppl (op, v1, v2)

let and' v1 v2 = InfixAppl (Binary.LogicalAnd, v1, v2)

let or' v1 v2 = InfixAppl (Binary.LogicalOr, v1, v2)

let equal v1 v2 = InfixAppl (Binary.Equal, v1, v2)

let not' v1 = UnaryAppl (Unary.Not, v1)

let tuple v = TupleLit v

let tuple_singleton v = tuple [v]

let rec of_sugar (_, phrase) =
  let module LPS = Phrase_sugar in
  match phrase with
  | LPS.Constant c -> Constant c
  | LPS.InfixAppl (op, p, q) -> InfixAppl (op, of_sugar p, of_sugar q)
  | LPS.UnaryAppl (op, p) -> UnaryAppl (op, of_sugar p)
  | LPS.Var v -> Var v

let rec traverse expr ~f =
  let fn expr' = traverse expr' ~f in
  let expr =
    match expr with
    | Constant _ -> expr
    | Var _ -> expr
    | UnaryAppl (a, arg) ->
        let arg = fn arg in
        UnaryAppl (a, arg)
    | InfixAppl (a, a1, a2) ->
        let a1 = fn a1 in
        let a2 = fn a2 in
        InfixAppl (a, a1, a2)
    | TupleLit [x] ->
        let x = fn x in
        TupleLit [x]
    | Case (phr, cases, otherwise) ->
        let phr = Option.map ~f:fn phr in
        let cases = List.map ~f:(fun (inp, lst) -> (fn inp, fn lst)) cases in
        let otherwise = fn otherwise in
        Case (phr, cases, otherwise)
    | _ -> failwith "Unknown operation"
  in
  f expr

let get_vars expr =
  let cols = ref Alias.Set.empty in
  let _ =
    traverse expr ~f:(fun expr ->
        match expr with
        | Var n ->
            cols := Alias.Set.add n !cols ;
            expr
        | _ -> expr )
  in
  !cols

let rename_var expr ~replace =
  traverse expr ~f:(fun expr ->
      match expr with
      | Var key ->
          Alias.Map.find ~key replace
          |> Option.map ~f:var |> Option.value ~default:expr
      | _ -> expr )

module Constant = struct
  let bool v = Constant (Value.Bool v)

  let int v = Constant (Value.Int v)

  let float v = Constant (Value.Float v)

  let string v = Constant (Value.String v)

  let of_value v = Constant v
end

let replace_var expr ~replace =
  traverse expr ~f:(fun expr ->
      match expr with
      | Var key ->
          Alias.Map.find ~key replace
          |> Option.map ~f:Constant.of_value
          |> Option.value ~default:expr
      | _ -> expr )

let[@inline always] val_typ_cmp cmp_b cmp_i cmp_f cmp_c cmp_s v1 v2 =
  let v =
    match (v1, v2) with
    | Value.Bool v, Value.Bool v' -> cmp_b v v'
    | Value.Char v, Value.Char v' -> cmp_c v v'
    | Value.Int v, Value.Int v' -> cmp_i v v'
    | Value.Float v, Value.Float v' -> cmp_f v v'
    | Value.String v, Value.String v' -> cmp_s v v'
    | _ -> failwith "Type comparison mismatch."
  in
  Value.box_bool v

let[@inline always] val_numeric op_i op_f v1 v2 =
  match (v1, v2) with
  | Value.Int v, Value.Int v' -> op_i v v' |> Value.box_int
  | Value.Float v, Value.Float v' -> op_f v v' |> Value.box_float
  | _ -> failwith "Type comparison mismatch."

let rec eval expr get_val =
  let open Value in
  match expr with
  | Constant c -> c
  | Var v -> (
    try get_val v with Not_found ->
      failwith ("Could not find column " ^ v ^ ".") )
  | InfixAppl (op, a1, a2) -> (
      let a1 = eval a1 get_val in
      let a2 = eval a2 get_val in
      match op with
      | Binary.GreaterEqual ->
          val_typ_cmp ( >= ) ( >= ) ( >= ) ( >= ) ( >= ) a1 a2
      | Binary.Greater -> val_typ_cmp ( > ) ( > ) ( > ) ( > ) ( > ) a1 a2
      | Binary.LessEqual ->
          val_typ_cmp ( <= ) ( <= ) ( <= ) ( <= ) ( <= ) a1 a2
      | Binary.Less -> val_typ_cmp ( < ) ( < ) ( < ) ( < ) ( < ) a1 a2
      | Binary.Equal -> val_typ_cmp ( = ) ( = ) ( = ) ( = ) ( = ) a1 a2
      | Binary.LogicalAnd -> box_bool (unbox_bool a1 && unbox_bool a2)
      | Binary.LogicalOr -> box_bool (unbox_bool a1 || unbox_bool a2)
      | Binary.Plus -> val_numeric ( + ) ( +. ) a1 a2
      | Binary.Multiply ->
          val_numeric (fun v v' -> v * v') (fun v v' -> v *. v') a1 a2
      | Binary.Minus -> val_numeric ( - ) ( -. ) a1 a2
      | Binary.Divide -> val_numeric ( / ) ( /. ) a1 a2 )
  | TupleLit l -> eval (List.hd l) get_val
  | UnaryAppl (op, arg) -> (
    match op with
    | Unary.Not ->
        let res = eval arg get_val in
        let res = not (unbox_bool res) in
        box_bool res
    | Unary.Minus -> (
        let res = eval arg get_val in
        match res with
        | Value.Float v -> -.v |> box_float
        | Value.Int v -> -v |> box_int
        | _ ->
            failwith
              (Format.asprintf
                 "Value '%a' does not support the unary minus operator."
                 Value.pp res) ) )
  | In (names, vals) ->
      let find = List.map ~f:get_val names in
      let equal s t = List.for_all2_exn ~f:Value.equal s t in
      let res = List.mem ~equal vals find in
      box_bool res
  | Case (inp, cases, otherwise) -> (
      let inp =
        match inp with None -> Value.Bool true | Some inp -> eval inp get_val
      in
      match List.find ~f:(fun (k, _v) -> eval k get_val = inp) cases with
      | Some (_, v) -> eval v get_val
      | None -> eval otherwise get_val )

module Option = struct
  type elt = t

  type t = elt option

  let combine_and phrase1 phrase2 =
    let tup_or x =
      match x with
      | InfixAppl (Binary.LogicalOr, _, _) -> tuple_singleton x
      | _ -> x
    in
    Option.combine
      ~f:(fun v1 v2 -> and' (tup_or v1) (tup_or v2))
      phrase1 phrase2

  let combine_or phrase1 phrase2 = Option.combine ~f:or' phrase1 phrase2

  let in_expr names vals =
    if names = [] then None
    else if vals = [] then Some (Constant.bool false)
    else Some (In (names, vals))
  let eval phrase f =
    match phrase with
    | Some phrase -> eval phrase f
    | None -> Phrase_value.box_bool true

  let get_vars phrase =
    Option.map ~f:(get_vars) phrase |> Option.value ~default:Alias.Set.empty
end

module Record = struct
  type record = Value.t

  module Record = Value.Record

  let eval t r =
    let get_val key = Record.get_exn ~key r in
    eval t get_val

  let matching_cols_simp on row =
    let phrase =
      List.fold_left
        (fun phrase (on, v) ->
          let term = Some (equal (var on) (Constant.of_value v)) in
          Option.combine_and phrase term )
        None (List.zip_exn on row)
    in
    phrase

  let matching_cols on row =
    let phrase =
      List.fold_left
        (fun phrase on ->
          let term =
            Some
              (equal (var on) (Record.get_exn row ~key:on |> Constant.of_value))
          in
          Option.combine_and phrase term )
        None (Alias.Set.elements on)
    in
    phrase
end

module List = struct
  type elt = t

  type t = elt list

  let fold_and l =
    List.fold_left
      (fun phrase term -> Option.combine_and phrase (Some term))
      None l

  let fold_and_opt l = List.filter_opt l |> fold_and

  let fold_or phrases =
    let ored =
      List.fold_left
        (fun phrase term -> Option.combine_or phrase (Some term))
        None phrases
    in
    match ored with None -> Some (Constant.bool false) | _ -> ored

  let fold_or_opt l = List.filter_opt l |> fold_or
end

module O = struct
  let ( > ) a b = infix (Operators.Binary.of_string ">") a b

  let ( < ) a b = infix (Operators.Binary.of_string "<") a b

  let ( = ) a b = infix (Operators.Binary.of_string "=") a b

  let ( && ) a b =
    infix Binary.LogicalAnd a b

  let ( || ) a b =
    infix Binary.LogicalOr a b

  let v a = var a

  let i v = Constant.int v

  let b b = Constant.bool b
end

module Grouped_variables = struct
  type phrase = t

  module Inner = Alias.Set
  include Set.Make (Inner)

  let times s1 s2 = fold (fun e acc -> map (Inner.union e) acc) s1 s2

  let of_lists l = Lens_list.map ~f:Inner.of_list l |> of_list

  let rec gtv p =
    match p with
    | Var v -> Inner.singleton v |> singleton
    | Constant _ -> singleton Inner.empty
    | InfixAppl (Binary.LogicalAnd, p1, p2) ->
        let s1 = gtv p1 in
        let s2 = gtv p2 in
        union s1 s2
    | InfixAppl (_, p1, p2) ->
        let s1 = gtv p1 in
        let s2 = gtv p2 in
        times s1 s2
    | _ -> failwith "Grouped type variables does not support this operator."

  let has_partial_overlaps t ~cols =
    exists
      (fun gr ->
        let int_not_empty = Inner.inter gr cols |> Inner.is_empty |> not in
        let diff_not_empty = Inner.diff gr cols |> Inner.is_empty |> not in
        int_not_empty && diff_not_empty )
      t
end
