(* Side-effect-free JSON operations. *)
open ProcessTypes
open Utility
open Types
open LensFDHelpers

(* Setting *)
let show_json = Basicsettings.Json.show_json

(* Type synonyms *)
type handler_id = int
type websocket_url = string

(* Types *)
type json_string = string

let parse_json str =
  Jsonparse.parse_json Jsonlex.jsonlex (Lexing.from_string str)

let parse_json_b64 str = parse_json(Utility.base64decode str)

let nil_literal = "null"


let js_dq_escape_string str =
  (* escape for placement in double-quoted string *)
  Str.global_replace (Str.regexp_string "\"") "\\\""
    (Str.global_replace (Str.regexp_string "\n") "\\n"
       (Str.global_replace (Str.regexp_string "\\") "\\\\"
          str))


(** Escape the argument for inclusion in a double-quoted string. *)
let js_dq_escape_char =
  function
    '"' -> "\\\""
  | '\\' -> "\\\\"
  | ch -> String.make 1 ch

type json_node_type = 
   [ `String 
   | `Unquoted
   ]

type writefn = string -> unit

let json_unquoted v (wr : writefn) = 
	wr v

let json_str v (wr : writefn) =
    wr "\"";
    js_dq_escape_string v |> wr;
    wr "\""

let json_int v (wr : writefn) =
    string_of_int v |> wr

let json_attr_unquoted key value (wr : writefn) =
    wr key;
    wr ": ";
    value wr

let json_node attributes (wr : writefn) =  
    wr "{";
    List.iteri (fun i (k,v) ->
        if i > 0 then wr ", ";
        json_attr_unquoted k v wr;
    ) attributes;
    wr "}"

let json_list elems (wr : writefn) =
    wr "[";
    List.iteri (fun i v ->
        if i > 0 then wr ", ";
        v wr
    ) elems;
    wr "]"

let json_bool (b : bool) (wr : writefn) =
    string_of_bool b |> wr

let json_constant (const : Constant.constant) (wr : writefn) =
    match const with
    | `Float f -> string_of_float' f |> wr
    | `Int i -> json_int i wr 
    | `Bool b -> json_bool b wr
    | `Char c -> json_node [("_c", js_dq_escape_char c |> json_str)] wr
    | `String s -> json_str s wr
    
let rec json_phrase (phrase : Types.lens_phrase) (wr : writefn) =
    match phrase with
    | `Constant c -> json_constant c wr
    | `Var v -> json_node [("_var", json_str v)] wr
    | `InfixAppl (op, l, r) -> json_node [
        ("_infx", Operators.string_of_binop op |> json_str);
        ("_l", json_phrase l);
        ("_r", json_phrase r)
    ] wr
    | `UnaryAppl (op, l) -> json_node [
        ("_op", Operators.string_of_unary_op op |> json_str);
        ("_l", json_phrase l)
    ] wr
    | `In (attrs, vals) -> json_node [
        ("_in", json_list (List.map json_str attrs));
        ("_vals", json_list (List.map (List.map json_constant ->- json_list) vals)) 
    ] wr 
    (* | `Case (phrase, cases, default) -> 
        let nodes = List.concat [ ] *)
                


let expand v = 
    let buf = Buffer.create 256 in
    let wr = Buffer.add_string buf in
    v wr;
    Buffer.contents buf

let json_col (col : Types.lens_col) =
   json_node [
      ("_table", json_str col.table);
      ("_name", json_str col.name);
      ("_alias", json_str col.alias);
      ("_typ", json_str <| Types.string_of_datatype col.typ);
      ("_present", json_bool col.present)]

let json_cols (cols : Types.lens_col list) =
  List.map json_col cols |> json_list

let json_sort (fundeps, phrase, cols : Types.lens_sort) =
  let json_of_key k = ColSet.elements k |> List.map json_str |> json_list in
  let json_of_fd (fd : fundep) = json_list [FunDep.left fd |> json_of_key; FunDep.right fd |> json_of_key] in
  let json_of_fds (fds : fundepset) = FunDepSet.elements fds |> List.map json_of_fd |> json_list in
  match phrase with 
  | None ->
     json_node [
        ("_fds", json_of_fds fundeps);
        ("_cols", json_cols cols)
     ]
  | Some phrase ->
     json_node [
        ("_fds", json_of_fds fundeps);
        ("_phrase", json_phrase phrase);
        ("_cols", json_cols cols)
     ]


let json_location (loc : Ir.location) =
  match loc with
  | `Client  -> json_str "client"
  | `Server  -> json_str "server"
  | `Native  -> json_str "native"
  | `Unknown -> json_str "unknown"

(* Helper functions for jsonization *)
(*
  SL:
    Having implemented jsonisation of database values, I'm now
    unsure if this is what we really want. From a security point
    of view it certainly isn't a very good idea to pass this kind of
    information to the client.
*)
let json_db (db, params) =
  let driver = db#driver_name() in
  let (name, args) = Value.parse_db_string params in
  json_node [
	("_db", json_node [
		("driver", json_str driver);
		("name", json_str name);
        ("args", json_str args)
	])
  ]

(*
WARNING:
  May need to be careful about free type variables / aliases in row
*)
let json_table ((db, params), name, keys, row) =
  let json_of_key k = List.map json_str k |> json_list in
  let json_of_keylist ks = json_list (List.map json_of_key ks) in
  json_node [
    ("_table", json_node [
      ("db", json_db (db, params));
      ("name", json_str name);
      ("row", Types.string_of_datatype (`Record row) |> json_str);
      ("keys", json_of_keylist keys)
    ])
  ]

let rec json_value' (v : Value.t) (wr : writefn) =
  match v with
  | `PrimitiveFunction _
  | `Resumption _
  | `Continuation _
  | `Socket _
      as r ->
      failwith ("Can't jsonize " ^ Value.string_of_value r);
  | `FunctionPtr (f, fvs) ->
    let (_, _, _, location) = Tables.find Tables.fun_defs f in
    let nodes = [
        ("func", Js.var_name_var f |> json_str);
        ("location", json_location location);
    ] in
    let nodes =
        match fvs with
        | None -> nodes
        | Some fvs -> List.append nodes [("environment", json_value' fvs)] in
    json_node nodes wr
  | `ClientDomRef i -> json_node [("_domRefKey", json_int i)] wr 
  | `ClientFunction name -> json_node [("func", json_str name)] wr 
  | #Value.primitive_value as p -> json_primitive p wr
  | `Variant (label, value) ->
        json_node [
            ("_label", json_str label);
            ("_value", json_value' value)
        ] wr
  | `Record fields ->
        let nodes = List.map (fun (k,v) -> (k, json_value' v)) fields in
        json_node nodes wr
  | `List l -> json_list (List.map json_value' l) wr
  | `AccessPointID (`ClientAccessPoint (cid, apid)) ->
		json_node [
			("_clientAPID", AccessPointID.to_json apid |> json_unquoted);
			("_clientId", ClientID.to_json cid |> json_unquoted)
		] wr
  | `AccessPointID (`ServerAccessPoint (apid)) ->
		json_node [ ("_serverAPID", AccessPointID.to_json apid |> json_unquoted) ] wr
  | `Pid (`ClientPid (client_id, process_id)) ->
		json_node [ 
			("_clientPid", ProcessID.to_json process_id |> json_unquoted);
			("_clientId", ClientID.to_json client_id |> json_unquoted)
		] wr
  | `Pid (`ServerPid (process_id)) ->
		json_node [ 
			("_serverPid", ProcessID.to_json process_id |> json_unquoted);
		] wr
  | `SessionChannel (ep1, ep2) ->
		json_node [ 
			("_sessEP1", ChannelID.to_json ep1 |> json_unquoted);
			("_sessEP2", ChannelID.to_json ep2 |> json_unquoted);
		] wr
  | `SpawnLocation (`ClientSpawnLoc client_id) ->
		json_node [ 
			("_clientSpawnLoc", ClientID.to_json client_id |> json_unquoted);
		] wr
  | `SpawnLocation (`ServerSpawnLoc) ->
		json_node [ 
			("_serverSpawnLoc", json_unquoted "[]");
		] wr
  | `Lens (t, sort) -> json_node [
     ("_lens", json_table t);
     ("_sort", json_sort sort);
   ] wr
and json_primitive (v : Value.primitive_value) (wr : writefn) =
  match v with
  | `Bool value -> json_bool value wr
  | `Int value -> json_int value wr
  | `Float value -> string_of_float' value |> wr
  | `Char c -> json_node [("_c", js_dq_escape_char c |> json_str)] wr
  | `Database db -> json_db db wr
  | `Table t -> json_table t wr
  | `XML xmlitem -> json_xmlitem xmlitem wr
  | `String s -> json_str s wr
and json_xmlitem xml (wr : writefn) = 
  match xml with
  | Value.Text s ->
      json_node [
        ("type", json_str "TEXT");
        ("text", json_str s);
      ] wr
  (* TODO: check that we don't run into problems when HTML containing
     an event handler is copied *)
  | Value.NsNode (ns, tag, xml) ->
      (* split into attributes and children *)
      let attrs, body =
        List.fold_right (fun xmlitem (attrs, body) -> 
          match xmlitem with 
          | Value.Attr (label, value) -> (label, json_str value) :: attrs, body
          | Value.NsAttr (ns, label, value) -> 
            ("\"" ^ ns ^ ":" ^ label ^ "\"", json_str value) :: attrs, body
          | _ -> attrs, json_xmlitem xmlitem :: body
        ) xml ([], []) in
      let nodes = [
        ("type", json_str "ELEMENT");
        ("tagName", json_str tag);
      ] in
      (* append namespace if present *)
	  let nodes = 
        if (String.length(ns) > 0) then
		  List.append nodes ["namespace", json_str ns]
        else
          nodes in
      (* add attributes and children *)
      let nodes = List.append nodes [
        ("attrs", json_node attrs);
        ("children", json_list body)
      ] in
      json_node nodes wr
  | Value.Node (name, children) -> 
    json_xmlitem (Value.NsNode ("", name, children)) wr
  | _ -> failwith "Cannot jsonize a detached attribute."
and json_values (vs : Value.t list) =
  List.map json_value' vs |> json_list

let show_processes procs =
  (* Show the JSON for a prcess, including the PID, process to be run, and mailbox *)
  let show_process (pid, (proc, msgs)) =
	json_node [
      ("pid", ProcessID.to_json pid |> json_unquoted);
      ("process", json_value' proc);
      ("messages", json_list (List.map json_value' msgs));
    ] in
  let bnds = PidMap.bindings procs in
  List.map show_process bnds |> json_list

let show_handlers evt_handlers =
  (* Show the JSON for an event handler: the evt handler key, and the associated process(es) *)
  let show_evt_handler (key, proc) =
    (* If the list of processes handling each key is represented by a 'List term, we translate it to a
       JS Array. This Array is supposed to be processes  by jslib code only*)
    let json_handler_list = function
      | `List elems -> List.map json_value' elems |> json_list
      | _ ->  json_value' proc in
    json_node [
      ("key", json_int key);
      ("eventHandlers", json_handler_list proc)
    ] in
  let bnds = IntMap.bindings evt_handlers in
  List.map show_evt_handler bnds |> json_list

let show_aps aps =
  let ap_list = AccessPointIDSet.elements aps in
  List.map (AccessPointID.to_json ->- json_unquoted) ap_list |> json_list

let show_buffers bufs =
  let json_buf (endpoint_id, values) = 
    let json_vals = List.map json_value' values |> json_list in
    json_node [
       ("buf_id", ChannelID.to_json endpoint_id |> json_unquoted);
       ("values", json_vals);
    ] in
  ChannelIDMap.bindings bufs |> List.map json_buf |> json_list

let print_json_state client_id conn_url procs handlers aps bufs =
  let ws_url_data =
    match conn_url with
    | Some ws_conn_url -> [
      ("ws_conn_url", json_str ws_conn_url)
    ]
    | None -> [] in
  let nodes = List.concat [
    [("client_id", ClientID.to_json client_id |> json_unquoted)];
    ws_url_data;
    [
      ("access_points", show_aps aps);
      ("buffers", show_buffers bufs);
      ("processes", show_processes procs);
      ("handlers", show_handlers handlers);
    ]
  ] in
  json_node nodes
     
let value_with_state v s =
  json_node [
    ("value", v);
    ("state", s);
  ]

(* JSON state definition *)
module JsonState = struct
  type t = {
    client_id : client_id;
    ws_conn_url : websocket_url option;
    processes: (Value.t * Value.t list) pid_map;
    buffers : Value.t list channel_id_map;
    channels : Value.chan list;
    handlers: Value.t intmap;
    aps: apid_set
  }

  (** Creates an empty JSON state *)
  let empty cid url = {
    client_id = cid;
    ws_conn_url = url;
    processes = PidMap.empty;
    buffers = ChannelIDMap.empty;
    channels = [];
    handlers = IntMap.empty;
    aps = AccessPointIDSet.empty
  }

  (** Adds a process and its mailbox to the state. *)
  let add_process pid proc mb state =
    { state with processes = PidMap.add pid (proc, mb) state.processes }

  (** Adds an event handler to the state *)
  let add_event_handler handler_id handler_val state =
    { state with handlers = IntMap.add handler_id handler_val state.handlers }

  (** Adds an access point ID to the state *)
  let add_ap_id apid state =
    { state with aps = AccessPointIDSet.add apid state.aps }

  (** Adds a buffer to the state *)
  let add_buffer chan_id buf state =
    { state with buffers = ChannelIDMap.add chan_id buf state.buffers }

  let add_carried_channel chan state =
    { state with channels = chan :: state.channels }

  let get_carried_channels state = state.channels

  (** Serialises the state as a JSON string *)
  let to_json s = print_json_state s.client_id s.ws_conn_url s.processes s.handlers s.aps s.buffers

  let to_string s = to_json s |> expand 

  let _merge s s' =
    let select_left _ x _ = Some x in
    let processes = PidMap.union select_left s.processes s'.processes in
    let buffers   = ChannelIDMap.union select_left s.buffers s'.buffers in
    let channels  =
      List.fold_left
        (fun acc chan ->
          (* make sure each channel only appears once *)
          chan :: List.filter (fun chan' -> chan <> chan') acc)
        s.channels s'.channels
    in
    let handlers = IntMap.union select_left s.handlers s'.handlers in
    (* TODO: access points *)
    let aps = AccessPointIDSet.union s.aps s'.aps in
    { s with processes = processes; buffers = buffers; channels = channels; handlers = handlers; aps = aps }
end

type json_state = JsonState.t

(* External interface *)
let jsonize_value_with_state value state =
  Debug.if_set show_json
      (fun () -> "jsonize_value_with_state => " ^ Value.string_of_value value);
  let jv = json_value' value in
  let jv_s = value_with_state jv (JsonState.to_json state) |> expand in
  Debug.if_set show_json (fun () -> "jsonize_value_with_state <= " ^ jv_s);
  jv_s

let jsonize_value v =
  Debug.if_set show_json
      (fun () -> "jsonize_value => " ^ Value.string_of_value v);
  let jv = json_value' v |> expand in
  Debug.if_set show_json (fun () -> "jsonize_value <= " ^ jv);
  jv


let encode_continuation (cont : Value.continuation) : string =
  Value.marshal_continuation cont

let jsonize_call s cont name args =
  let v = json_node [
    ("__continutation", encode_continuation cont |> json_str);
    ("__name", json_str name);
    ("__args", json_values args);
  ] in
  value_with_state v (JsonState.to_json s) |> expand

