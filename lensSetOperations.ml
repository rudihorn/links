open Value


module SortedRecords = struct 
    (* simplified record type drops column names for efficiency *)
    type simp_rec = Value.t list

    type recs = { columns: string list; plus_rows: simp_rec array; neg_rows: simp_rec array; }

    let is_positiv (t: recs) = 
        Array.length t.neg_rows = 0

    let compare_val (a : Value.t) (b : Value.t) : int =
        match a, b with 
        | `Bool b1, `Bool b2 -> compare b1 b2
        | `Char c1, `Char c2 -> compare c1 c2
        | `Float f1, `Float f2 -> compare f1 f2
        | `Int i1 , `Int i2 -> compare i1 i2
        | `String i1 , `String i2 -> compare i1 i2
        | _, _ -> failwith "Unsupported comparison types."

    let compare (a : simp_rec) (b : simp_rec) : int =
        match a, b with
        | x::xs, y::ys -> 
            match compare_val x y with
            | 0 -> compare xs ys 
            | a -> a
        | _ -> 0 (* if either of the lists are empty, return match
                    this allows us to perform partial matching *)


    (* records: List of records *)
    let construct (records : Value.t) =
        let l = unbox_list records in
        let recs = List.map unbox_record l in
        let keys = List.map (fun (k,v) -> k) (List.hd recs) in
        let simpl_rec r = List.map2 (fun a (k,v) -> if a = k then v else failwith "List columns not consistent") keys r in
        let recs = Array.of_list (List.map simpl_rec recs) in
        Array.sort compare recs;
        { columns = keys; plus_rows = recs; neg_rows = Array.of_list []; }
        
    let to_string (rs : recs) =
        let cols = rs.columns in
        let row_to_string row = 
            List.fold_left (fun a (k,v) ->
                let str = k ^ ": " ^ string_of_value v in
                let str = "(" ^ str ^ ")" in
                if a = "" then str else a ^ ", " ^ str) "" (List.combine cols row) in
        let pos = Array.fold_left (fun a row ->
            let str = row_to_string row in
            if a = "" then str else
                a ^ "\n" ^ str) "" rs.plus_rows in
        pos 

    let to_string_tabular (rs : recs) =
        let pad a b = Pervasives.max 0 (a - b) in
        let cols = rs.columns in
        let cols = List.map (fun c ->
            c ^ (String.make (pad 8 (String.length c)) ' ')) cols in
        let row_to_string row = 
            List.fold_left (fun a (k,v) ->
                let str = string_of_value v in
                let str = str ^ (String.make (pad (String.length k + 1) (String.length str)) ' ') in
                if a = "" then str else a ^ "| " ^ str) "" (List.combine cols row) in
        let cols_string = List.fold_left(fun a k -> 
                if a = "" then k else a ^ " | " ^ k) "" cols in
        let sep = String.map (fun _ -> '-') cols_string in
        let pos = Array.fold_left (fun a row ->
            let str = row_to_string row in
            if a = "" then str else
                a ^ "\n" ^ str) (cols_string ^ "\n" ^ sep) rs.plus_rows in
        pos 

    let find_mul (rs : simp_rec array) (r : simp_rec) : bool =
        let rec pivot s e =
            if s > e then
                false
            else
                let m = (s + e) / 2 in
                let r = compare (Array.get rs m) r in
                match r with
                | 0 -> true
                | a when a > 0 -> pivot s (m-1)
                | a when a < 0 -> pivot (m+1) e in
        let r = pivot 0 ((Array.length rs) - 1) in
        r

    let find (rs : recs) (r : simp_rec) : bool =
        find_mul rs.plus_rows r

    let get_col_map (rs : recs) (col : string) =
        let cols = rs.columns in
        let rec fn cols = 
            match cols with 
            | x::xs -> 
                if x = col then 
                    Some (fun x -> List.hd x) 
                else 
                    begin
                        let fn2 = fn xs in
                        match fn2 with
                        | Some fn2 -> Some (fun x -> fn2 (List.tl x))
                        | None -> None
                    end
            | _ -> None in
        fn cols

    let get_cols_map (rs : recs) (cols : string list) =
        let maps = List.map (fun col -> get_col_map rs col) cols in
        let maps = List.flatten (List.map (fun mp -> match mp with None -> [] | Some a -> [a]) maps) in
        (fun r -> List.map (fun mp -> mp r) maps)

    let project_onto (rs : recs) (cols : string list) =
        let maps = get_cols_map rs cols in
        let maps2 = get_cols_map rs cols in
        let plus_rows = Array.map maps rs.plus_rows in
        let neg_rows = Array.map maps rs.neg_rows in
        let cols = maps2 rs.columns in
        Array.sort compare plus_rows;
        Array.sort compare neg_rows;
        { columns = cols; plus_rows = plus_rows; neg_rows = neg_rows }

    let project_onto_set (rs : recs) (rs2 : recs) = 
        project_onto rs (rs2.columns) 

    let not_neg_empty (rs : recs) = 
        (rs.neg_rows <> Array.of_list [])

    let minus (rs1 : recs) (rs2 : recs) =
        if not_neg_empty rs2 then
            failwith "Cannot subtract from negative multiplicities"
        else
            let rec get_map col cols =
                match cols with 
                | x::xs -> 
                    if x = col then 
                        Some (fun x -> List.hd x) 
                    else 
                        begin
                            let fn2 = get_map col xs in
                            match fn2 with
                            | Some fn2 -> Some (fun x -> fn2 (List.tl x))
                            | None -> None
                        end
                | _ -> None in
            let proj = project_onto_set rs2 rs1 in
            let maps = List.map (fun c -> match get_map c rs1.columns with None -> [] | Some a -> [a]) proj.columns in
            let maps = List.flatten maps in
            print_endline (to_string_tabular proj);
            let rows = List.filter (fun r -> not (find proj (List.map (fun mp -> mp r) maps))) (Array.to_list rs1.plus_rows) in
            { rs1 with plus_rows = Array.of_list rows }

    let merge (rs1 : recs) (rs2 : recs) =
        let proj = project_onto_set rs2 rs1 in
        if rs1.columns <> proj.columns then
            failwith "cannot merge two different sets"
        else
            let rows_rs1 = List.filter (fun r -> not (find_mul proj.neg_rows r)) (Array.to_list rs1.plus_rows) in
            let rows_rs1_n = List.filter (fun r -> not (find_mul rs1.plus_rows r)) (Array.to_list proj.neg_rows) in
            let rows_rs2 = List.filter (fun r -> not (find_mul rs1.neg_rows r)) (Array.to_list proj.plus_rows) in
            let rows_rs2_n = List.filter (fun r -> not (find_mul proj.plus_rows r)) (Array.to_list rs1.neg_rows) in
            let rows_rs1 = Array.of_list rows_rs1 in
            let rows_rs1_n = Array.of_list rows_rs1_n in
            (* remove duplicate rows *)
            let rows_rs2 = List.filter (fun r -> not (find_mul rows_rs1 r)) rows_rs2 in
            let rows_rs2_n = List.filter (fun r -> not (find_mul rows_rs1_n r)) rows_rs2_n in
            let rows = Array.append rows_rs1 (Array.of_list rows_rs2) in
            let rows_n = Array.append rows_rs1_n (Array.of_list rows_rs2_n) in
            { columns = rs1.columns; plus_rows = rows; neg_rows = rows_n }

    let box_simp_rec (cols : string list) (vals : Value.t list) =
        box_value (List.combine cols vals)
end
