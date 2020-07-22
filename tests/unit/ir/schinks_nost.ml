open Links_core
open State.Syntax

module CT = CommonTypes

module St = struct
  type t = { next_id : int }

  let fresh =
    let* st = State.get in
    let id = st.next_id in
    let+ () = State.map_state (fun _ -> { next_id = id + 1 }) in
    id
end

let mk_primitive p = Types.Primitive p

module T = struct
  let int = mk_primitive CT.Primitive.Int
  let bool = mk_primitive CT.Primitive.Bool
  let string = mk_primitive CT.Primitive.Bool
end

let var id = Ir.Variable id |> State.return

let fresh_var =
  let+ id = St.fresh in
  var id

let binder id ?(scope = Var.Scope.Local) ty =
  let fake_name = Printf.sprintf "gen_%d" id in
  let var_info = Var.make_info ty fake_name scope in
  Var.make_binder id var_info

let bind ty ?(scope = Var.Scope.Local) body =
  let* id = St.fresh in
  let* body = body in
  let bnd = binder id ~scope ty in
  let+ v = var id in
  (Ir.Let (bnd, ([], body)), v)

let mk_const c = Ir.Constant c |> State.return

let s str = mk_const (CT.Constant.String str)

let apply f args =
  let* f = f in
  let+ args = State.List.lift args in
  Ir.Apply (f, args)

let apply1 f arg = apply f [ arg ]

let return v =
  let+ v = v in
  Ir.Return v

let def ty ?(tparams = []) params ?closure_var ?(location = CT.Location.Server)
    ?(unsafe_sig = false) body =
  let* id = St.fresh in
  let bin = binder id ty in
  let* params = State.List.lift params in
  let* cv_binder = State.Option.lift closure_var in
  let+ body = body in
  (bin, (tparams, params, body), cv_binder, location, unsafe_sig)

let fun_ ty ?tparams params ?closure_var ?location ?unsafe_sig body =
  let+ df = def ty ?tparams params ?closure_var ?location ?unsafe_sig body in
  Ir.Fun df

module Computation = struct
  let ( let$* ) v f =
    let* b, v = v in
    let+ bs, n = f (v |> State.return) in
    (b :: bs, n)

  let ( let$+ ) v f =
    let* b, v = v in
    let+ n = f (v |> State.return) in
    ([ b ], n)
end

let unbound =
  let+ v = fresh_var in
  v

let _comp =
  let* f = unbound in
  let+ g = unbound in
  fun_ T.int []
    Computation.(
      let$* x = bind T.string (apply1 g (s "foo")) in
      let$+ y = bind T.int (apply1 f x) in
      return y)
