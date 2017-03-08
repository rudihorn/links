open Types
open Utility

type fd_node = [
    | `FDNode of (string list) * (fd_node list)
]

let fd_left (fd_left, _ : Types.fn_dep) = fd_left

let fd_right (_, fd_right : Types.fn_dep) = fd_right

let fdnode_left (fd : fd_node) = match fd with
    | `FDNode (l, _) -> l

let fdnode_right (fd : fd_node) = match fd with
    | `FDNode (_, l) -> l

let contains_all a b = 
    List.for_all (fun bel ->
        List.mem bel a
    ) b

let get_fd_root (fds : Types.fn_dep list) = 
    List.find (fun fd ->
        not (List.exists (fun fd2 ->
            contains_all (fd_right fd2) (fd_left fd)) fds
        )
    ) fds

let rec get_fd_subnodes (fd : Types.fn_dep) (fds : Types.fn_dep list) : fd_node = 
    let subfds = List.filter (fun fd2 ->
        contains_all (fd_right fd) (fd_left fd2)
    ) fds in
    let remaining = List.filter (fun col ->
        not (List.exists (List.mem col) (List.map fd_left subfds))) (fd_right fd) in
    let remaining = `FDNode (remaining, []) in
    let subfds = List.map (fun x -> get_fd_subnodes x fds) subfds in
        `FDNode (fd_left fd, remaining :: subfds)

let get_fd_tree (fds : Types.fn_dep list) = 
    let root = get_fd_root fds in
    let rootFDNode = get_fd_subnodes root fds in
        rootFDNode

let rec print_list (l : string list) (out : string -> unit) =
    match l with
    | x :: [] -> out x
    | x :: xs -> out (x ^ ", "); print_list xs out
    | [] -> out ""

let rec print_spacer (depth : int) (out : string -> unit) =
    match depth with 
    | 0 -> ()
    | n -> (out "  "); print_spacer (n - 1) out

let rec debug_print_fd_tree_ex (fd : fd_node) (depth : int) (out : string -> unit) =
    print_spacer depth out;
    out " - ";
    print_list (fdnode_left fd) out;
    out " -> \n";
    let _ = List.map (fun f -> debug_print_fd_tree_ex f (depth + 1) out) (fdnode_right fd) in
    ()

let debug_print_fd_tree (fd : fd_node) =
    let str = ref "" in
    let _ = debug_print_fd_tree_ex fd 0 (fun x -> str := !str ^ x) in
    Debug.print !str