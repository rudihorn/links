(*pp camlp4of *)

open Camlp4.PreCast

module InContext (C : sig val context : Base.context val loc : Camlp4.PreCast.Loc.t end) =
struct
  open C
  open Types
  open Utils
  open Base
  include Base.InContext(C)

  let classname = "Functor"

  let param_map : string NameMap.t = 
    List.fold_right
      (fun (name,_) map -> NameMap.add name ("f_" ^ name) map)
      context.params
      NameMap.empty

  let tdec, sigdec = 
    let dec name = 
      ("f", context.params, 
       `Expr (`Constr ([name], List.map (fun p -> `Param p) context.params)), [])
    in
      (fun name -> Untranslate.decl (dec name)),
      (fun name -> Untranslate.sigdecl (dec name))

  let wrapper name expr = 
    let patts :Ast.patt list = 
      List.map 
        (fun (name,_) -> <:patt< $lid:NameMap.find name param_map$ >>)
        context.params in
    let rhs = 
      List.fold_right (fun p e -> <:expr< fun $p$ -> $e$ >>) patts expr in
      <:module_expr< struct
        open Functor
        type $tdec name$ 
        let map = $rhs$
      end >>
(*
   prototype: [[t]] : t -> t[b_i/a_i]


   [[a_i]]   = f_i

   [[C1|...CN]] = function [[C1]] ... [[CN]]               sum
   [[`C1|...`CN]] = function [[`C1]] ... [[`CN]]           variant
 
   [[{t1,...tn}]] = fun (t1,tn) -> ([[t1]],[[tn]])         tuple
   [[{l1:t1; ... ln:tn}]] = 
         fun {l1=t1;...ln=tn} -> {l1=[[t1]];...ln=[[tn]]}  record

   [[(t1,...tn) c]] = c_map [[t1]]...[[tn]]                constructor

   [[a -> b]] = f . [[a]] (where a_i \notin fv(b))         function

   [[C0]]    = C0->C0                                      nullary constructors
   [[C1 (t1...tn)]]  = C1 t -> C0 ([[t1]] t1...[[tn]] tn)  unary constructor
   [[`C0]]   = `C0->`C0                                    nullary tag
   [[`C1 t]] = `C1 t->`C0 [[t]] t                          unary tag
*)
  let rec polycase = function
    | Tag (name, None) -> <:match_case< `$name$ -> `$name$ >>
    | Tag (name, Some e) -> <:match_case< `$name$ x -> `$name$ ($expr e$ x) >>
    | Extends t -> 
        let patt, guard, exp = cast_pattern context t in
          <:match_case< $patt$ when $guard$ -> $expr t$ $exp$ >>

  and expr : Types.expr -> Ast.expr = function
    | t when not (contains_tvars t) -> <:expr< fun x -> x >>
    | `Param (p,_) -> <:expr< $lid:NameMap.find p param_map$ >>
    | `Function (f,t) when not (contains_tvars t) -> 
        <:expr< fun f x -> f ($expr f$ x) >>
    | `Constr (qname, ts) -> 
        List.fold_left 
          (fun fn arg -> <:expr< $fn$ $expr arg$ >>)
          <:expr< $id:modname_from_qname ~qname ~classname$.map >>
          ts
    | `Tuple ts -> tup ts
    | _ -> raise (Underivable "Functor cannot be derived for this type")

  and tup ts = 
    let args, exps = 
        (List.fold_right2
           (fun t n (p,e) -> 
              let v = Printf.sprintf "t%d" n in
                Ast.PaCom (loc, <:patt< $lid:v$ >>, p),
                Ast.ExCom (loc, <:expr< $expr t$ $lid:v$ >>, e))
           ts
           (List.range 0 (List.length ts))
           (<:patt< >>, <:expr< >>)) in
    let pat, exp = Ast.PaTup (loc, args), Ast.ExTup (loc, exps) in
      <:expr< fun $pat$ -> $exp$ >>

  and case = function
    | (name, []) -> <:match_case< $uid:name$ -> $uid:name$ >>
    | (name, args) -> 
        let f = tup args 
        and tpatt, texp = tuple (List.length args) in
          <:match_case< $uid:name$ $tpatt$ -> let $tpatt$ = ($f$ $texp$) in $uid:name$ ($texp$) >>

  and field (name, (_,t), _) : Ast.expr =
    <:expr< $expr t$ $lid:name$ >>

  let rhs = function
    |`Fresh (_, Sum summands)  -> 
       <:expr<  function $list:List.map case summands$ >>
    |`Fresh (_, Record fields) -> 
       <:expr< fun $record_pattern fields$ -> 
                   $record_expr (List.map (fun ((l,_,_) as f) -> (l,field f)) fields)$ >>
    |`Expr e                  -> expr e
    |`Variant (_, tags) -> 
       <:expr< function $list:List.map polycase tags$ >>


  let maptype name = 
    let ctor_in = `Constr ([name], List.map (fun p -> `Param p) context.params) in
    let ctor_out = substitute param_map ctor_in  (* c[f_i/a_i] *) in
      List.fold_right (* (a_i -> f_i) -> ... -> c[a_i] -> c[f_i/a_i] *)
        (fun (p,_) out -> 
           (<:ctyp< ('$lid:p$ -> '$lid:NameMap.find p param_map$) -> $out$>>))
        context.params
        (Untranslate.expr (`Function (ctor_in, ctor_out)))

   let signature name : Ast.sig_item list =  
     [ <:sig_item< type $sigdec name$ >>; 
       <:sig_item< val map : $maptype name$ >> ] 

  let decl (name, _, r, _) : Camlp4.PreCast.Ast.module_binding =
      <:module_binding<
         $uid:classname ^ "_" ^ name$
       : sig $list:signature name$ end
       = $wrapper name (rhs r)$ >>
end

let _ = Base.register "Functor"
  (fun (loc, context, decls) ->
     let module F = InContext(struct let loc = loc and context = context end) in
       <:str_item< module rec $list:List.map F.decl decls$ >>)
