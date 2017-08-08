open Ast
open Expr
open Formula
open Dep

type modul = {
    imported: string list;
    (* ctx: (string*value) list; *)
    vars: (string, value) Hashtbl.t;
    functions: (string, ((pattern list) * expr)) Hashtbl.t;
}

type model = {
    (* transition: (pattern * expr); *)
    transition : pattern * ((expr * expr) list);
    fairness: formula list;
    properties: (string * formula) list;
}

type runtime = {
    moduls: (string, modul) Hashtbl.t;
    mutable model: model;
}

exception Evaluation_error of string
exception No_matched_pattern of value

type context = (string * value ref) list

let modify_ctx ctx str value = Refpairs.replace_first ctx str value
(* let add_to_ctx ctx str value = (str, value)::ctx *)

let rec value_of_str str runtime modul = 
    let m = Hashtbl.find runtime.moduls modul in
    if Hashtbl.mem m.vars str then
        Hashtbl.find m.vars str
    else begin
        let found_in_imported = ref false 
        and value = ref (VInt 0) in
        List.iter (fun mname -> 
            if not !found_in_imported then begin
                let m = Hashtbl.find runtime.moduls mname in
                if Hashtbl.mem m.vars str then begin
                    value := Hashtbl.find m.vars str;
                    found_in_imported := true
                end
            end
        ) m.imported;
        if !found_in_imported then
            !value
        else
            raise (Evaluation_error ("can not find binding of "^str))
    end

let rec value_of_str_path value strs =
    match strs with
    | [] -> value
    | str::strs' -> begin
            match value with
            | VRecord str_value_list -> 
                if Pairs.key_exists str_value_list str then
                    value_of_str_path (Pairs.get_value str_value_list str) strs'
                else
                    raise (Evaluation_error ((str_value value)^" does not have field "^str))
            | _ -> raise (Evaluation_error ((str_value value)^" should be a record with field "^str))
        end

let rec modified_record_value rv str_list value = 
    match str_list with
    | [] -> value
    | str::strs -> begin
            match rv with
            | VRecord str_value_list -> VRecord (Pairs.replace_first str_value_list str (modified_record_value (Pairs.get_value str_value_list str) strs value))
            | _ -> raise (Evaluation_error ((str_value rv)^" should be a record value."))
        end

let rec get_matched_pattern value pat_expr_list = 
    match value, pat_expr_list with
    | _, [] -> raise (No_matched_pattern value)
    | _, (Pat_Underline, expr)::pel -> [], expr
    | _, (Pat_Symbol str, expr)::pel -> [(str, ref value)], expr
    | VInt i, (Pat_Int j, expr)::pel -> if i = j then [], expr else get_matched_pattern value pel
    (* | VInt i, (Pat_Symbol str, expr)::pel -> [(str, VInt i)], expr *)
    | VFloat f, (Pat_Float g, expr)::pel -> if f = g then [], expr else get_matched_pattern value pel
    (* | VFloat f, (Pat_Symbol str, expr)::pel -> [(str, VFloat f)], expr *)
    | VUnt, (Pat_Unt, expr)::pel -> [], expr
    (* | VBool b, (VBool c, expr)::pel -> if b=c then [], expr else get_matched_pattern value pel *)
    | VAray vl, (Pat_Aray pl, expr)::pel 
    | VLst vl, (Pat_Aray pl, expr)::pel ->
        if List.length vl <> List.length pl then
            get_matched_pattern value pel
        else begin
            let ctx = ref [] in
            try
                for i = 0 to List.length vl - 1 do
                    let ctx0, _ = get_matched_pattern (List.nth vl i) [(List.nth pl i, expr)] in
                    ctx := !ctx @ ctx0    
                done;
                !ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel    
        end
    | VLst vl, (Pat_Lst_Cons (p1, p2), expr)::pel ->
        if List.length vl = 0 then
            get_matched_pattern value pel
        else begin
            try
                let vh, vt = List.hd vl, List.tl vl in
                let ctx1, _ = get_matched_pattern vh [(p1, expr)] 
                and ctx2, _ = get_matched_pattern (VLst vt) [(p2, expr)] in
                ctx1 @ ctx2, expr
            with No_matched_pattern _ -> get_matched_pattern value pel
        end
    | VTuple vl, (Pat_Tuple pl, expr)::pel ->
        if List.length vl <> List.length pl then
            get_matched_pattern value pel
        else begin
            let ctx = ref [] in
            try
                for i = 0 to List.length vl - 1 do
                    let ctx0, _ = get_matched_pattern (List.nth vl i) [(List.nth pl i, expr)] in
                    ctx := !ctx @ ctx0    
                done;
                !ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel    
        end
    | VConstr (str1, None), (Pat_Constr (str2, None), expr)::pel ->
        if str1 = str2 then
            [], expr
        else
            get_matched_pattern value pel
    | VConstr (str1, Some v1), (Pat_Constr (str2, Some p1), expr)::pel ->
        if str1 <> str2 then
            get_matched_pattern value pel
        else begin
            try
                let ctx, _ = get_matched_pattern v1 [(p1, expr)] in
                ctx, expr
            with No_matched_pattern _ -> get_matched_pattern value pel
        end
    | _, _::pel -> get_matched_pattern value pel

let find_function str runtime modul = 
    (* print_endline ("finding function "^str^" in modul "^modul); *)
    let m = Hashtbl.find runtime.moduls modul in
    if Hashtbl.mem m.functions str then
        Hashtbl.find m.functions str
    else begin
        let found = ref false in
        let f = ref ([], Int 0) in
        List.iter (fun mname ->
            if not !found then
                let m = Hashtbl.find runtime.moduls mname in
                if Hashtbl.mem m.functions str then
                    f := Hashtbl.find m.functions str
        ) m.imported;
        if !found then !f else raise (Evaluation_error ("function "^str^" is not defined in the scope of "^modul))
    end
        

        

let rec evaluate_seq exprs ctx runtime modul = 
  match exprs with
  | [] -> raise (Evaluation_error "error evaluating seq expr")
  | [e] -> evaluate e ctx runtime modul 
  | e :: es -> begin
      match e with
      (* | Val_binding (str, e1) -> evaluate_seq es (Refpairs.add_to_first ctx str (evaluate e1 ctx runtime modul)) runtime modul
      | Var_binding (str, e1) -> evaluate_seq es (Refpairs.add_to_first ctx str (evaluate e1 ctx runtime modul)) runtime modul *)
      | Let (p, e1) -> 
        let v = evaluate e1 ctx runtime modul in
        let ctx1,_ = get_matched_pattern v [(p, e1)] in
        evaluate_seq es (ctx1 @ ctx) runtime modul
      | _ -> let _ = evaluate e ctx runtime modul in evaluate_seq es ctx runtime modul
    end  
and evaluate expr ctx runtime modul = 
  match expr with
    | Int i -> VInt i
    | Float f -> VFloat f
    | Unt -> VUnt
    | Bool b -> VBool b
    | Symbol str_list -> begin
        match str_list with
        | [] -> raise (Evaluation_error "can not evaluate an empty symbol")
        | [str] -> 
            if str = (String.capitalize_ascii str) then
                raise (Evaluation_error ("can not evaluate a modul name as a symbol: "^str))
            else begin
                match Refpairs.find ctx str with
                | None -> value_of_str str runtime modul 
                | Some v -> v
            end 
        | str::strs ->
            if str = (String.capitalize_ascii str) then
                value_of_str_path (value_of_str (List.hd strs) runtime str) (List.tl strs)
            else if Pairs.key_exists ctx str then
                value_of_str_path (Refpairs.get_value ctx str) strs
            else
                value_of_str_path (value_of_str str runtime modul) strs
        end
    (* | Val_binding _ | Var_binding _ -> raise (Evaluation_error "should not bind variables in the last expression") *)
    | Let _ -> raise (Evaluation_error "should not bind variables in the last expression") 
    | Aray ea -> VAray (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Lst ea -> VLst (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Op (op, el) -> begin
            match op, el with
            | "[]", [e1; e2] -> 
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1,v2 with
                    | VAray va, VInt i -> List.nth va i
                    | _ -> raise (Evaluation_error ((str_value v1)^" should be an array value, and "^(str_value v2)^" should be an integer value."))
                end
            | "::", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v2 with
                    | VLst vl -> VLst (v1::vl)    
                    | _ -> raise (Evaluation_error ((str_value v2)^" should be a list value."))
                end
            | "!", [e1] ->
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VBool b -> VBool (not b)
                    | _ -> raise (Evaluation_error ((str_value v1)^" is not a bool value."))    
                end
            | "&&", [e1; e2] -> 
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VBool b1, VBool b2 -> VBool (b1 && b2)
                    | _ -> raise (Evaluation_error "can not evaluate to bool value.")    
                end
            | "||", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VBool b1, VBool b2 -> VBool (b1 || b2)
                    | _ -> raise (Evaluation_error "can not evaluate to bool value.")    
                end
            | "-", [e1] ->
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VInt i -> VInt (-i)
                    | _ -> raise (Evaluation_error ((str_value v1)^" is not a integer value."))    
                end
            | "-.", [e1] -> 
                let v1 = evaluate e1 ctx runtime modul in begin
                    match v1 with
                    | VFloat f -> VFloat (0. -. f)
                    | _ -> raise (Evaluation_error ((str_value v1)^" is not a float value."))    
                end
            | "+", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1+i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "+.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat f1, VFloat f2 -> VFloat (f1+.f2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "-", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1-i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "-.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat f1, VFloat f2 -> VFloat (f1-.f2)
                    | _ -> raise (Evaluation_error "can not evaluate to float value.")    
                end
            | "*", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VInt i1, VInt i2 -> VInt (i1*i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "*.", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in begin
                    match v1, v2 with
                    | VFloat i1, VFloat i2 -> VFloat (i1*.i2)
                    | _ -> raise (Evaluation_error "can not evaluate to integer value.")    
                end
            | "=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 = v2)
            | "!=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 <> v2)
            | "<", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 < v2)
            | "<=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 <= v2)
            | ">", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 > v2)
            | ">=", [e1; e2] ->
                let v1 = evaluate e1 ctx runtime modul 
                and v2 = evaluate e2 ctx runtime modul in
                VBool (v1 >= v2)
            | str, es ->
                let pats, e1 = find_function str runtime modul in
                if List.length es <> List.length pats then 
                    raise (Evaluation_error ("function "^str^" has "^(string_of_int (List.length pats))^" parameters, but is applied to "^(string_of_int (List.length es))^" arguments."))
                else begin
                    let ctx0 = ref [] in
                    for i = 0 to List.length es - 1 do
                        let e1 = List.nth es i in
                        let ctx1, _ = get_matched_pattern (evaluate e1 ctx runtime modul) [(List.nth pats i, e1)] in
                        ctx0 := ctx1 @ !ctx0
                    done;
                    evaluate e1 (!ctx0 @ ctx) runtime modul
                end
        end
    | Tuple ea -> VTuple (List.map (fun e -> evaluate e ctx runtime modul) ea)
    | Record str_expr_array -> VRecord ((List.map (fun (str, expr) -> str, evaluate expr ctx runtime modul) str_expr_array))
    | IF (e1, e2, None) ->
        let v1 = evaluate e1 ctx runtime modul in
        if v1 = VBool true then
            evaluate e2 ctx runtime modul
        else if v1 = VBool false then
            VUnt
        else
            raise (Evaluation_error ((str_value v1)^" should be a bool value."))
    | IF (e1, e2, Some e3) ->
        let v1 = evaluate e1 ctx runtime modul in
        if v1 = VBool true then
            evaluate e2 ctx runtime modul
        else if v1 = VBool false then
            evaluate e3 ctx runtime modul
        else
            raise (Evaluation_error ((str_value v1)^" should be a bool value."))
    | While (e1, e2) ->
        let v1 = ref (evaluate e1 ctx runtime modul) in
        while (!v1 = VBool true) do
            ignore(evaluate e2 ctx runtime modul);
            v1 := evaluate e1 ctx runtime modul
        done;
        VUnt
    | For (str, e1, e2, e3) ->
        let v1 = evaluate e1 ctx runtime modul 
        and v2 = evaluate e2 ctx runtime modul in begin
            match v1, v2 with
            | VInt i, VInt j -> 
                let ctx0 = Refpairs.add_to_first ctx str v1 in
                if i<=j then begin
                    for counter = i to j do
                        Refpairs.replace_first ctx0 str (VInt counter);
                        ignore(evaluate e3 ctx0 runtime modul)    
                    done;
                    VUnt
                end else begin
                    for counter = i downto j do
                        Refpairs.replace_first ctx0 str (VInt counter);
                        ignore(evaluate e3 ctx0 runtime modul)
                    done;
                    VUnt
                end
            | _ -> raise (Evaluation_error "error evaluating for expression.")    
        end
    | Seq es -> evaluate_seq es ctx runtime modul
    | Assign (e1, e2) -> begin
            match e1 with
            | Symbol str_list -> begin
                    match str_list with
                    | [] -> raise (Evaluation_error "can not assign to an empty symbol.")
                    | [str] -> modify_ctx ctx str (evaluate e2 ctx runtime modul); VUnt
                    | str::strs -> modify_ctx ctx str (modified_record_value (Refpairs.get_value ctx str) strs (evaluate e2 ctx runtime modul)); VUnt
                end
            | Op ("[]", [Symbol [s]; e3]) -> begin
                    if not (Pairs.key_exists ctx s) then
                        raise (Evaluation_error (s^" is not defined."));
                    match Refpairs.get_value ctx s with
                    | VAray vl -> begin
                            match evaluate e3 ctx runtime modul with
                            | VInt i -> 
                                if i > List.length vl then
                                    raise (Evaluation_error ("index out of bounds: "^(string_of_int i)));
                                let index = ref (-1) in 
                                let new_vl = List.map (fun v -> incr index; if !index = i then evaluate e2 ctx runtime modul else v) vl in
                                modify_ctx ctx s (VAray new_vl); VUnt
                            | _ -> raise (Evaluation_error ("can not evaluate to an int value: "^(str_expr e3)))
                        end 
                    | _ -> raise (Evaluation_error (s^" is not bounded to an array"))
                end
            | _ -> raise (Evaluation_error ("error evaluating assign expr."))
        end        
    | Match (e1, pat_expr_list) -> 
        let v1 = evaluate e1 ctx runtime modul in
        let ctx0, e1 = get_matched_pattern v1 pat_expr_list in
        evaluate e1 (ctx0 @ ctx) runtime modul
    | With (e1, str_expr_list) -> 
        let v1 = evaluate e1 ctx runtime modul in begin
            match v1 with
            | VRecord str_value_list -> VRecord (List.fold_left (fun svl (str, expr) -> Pairs.replace_first svl str (evaluate expr ctx runtime modul)) str_value_list str_expr_list)
            | _ -> raise (Evaluation_error ((str_value v1)^" should be a record value."))    
        end
    | Constr (str, None) -> VConstr (str, None)
    | Constr (str, Some e1) -> VConstr (str, Some (evaluate e1 ctx runtime modul))
            
let rec pfmll_to_fml pfmll runtime modul = 
  match pfmll.pfml with
  | PTop -> Top 
  | PBottom -> Bottom
  | PAtomic (str, pels) -> Atomic (str, List.map (fun pel -> 
        match pel.pexpr with
        | PSymbol [s] -> SVar s
        | _ -> State (evaluate (pexprl_to_expr pel) [] runtime modul)
    ) pels)
  | PNeg pfml1 -> Neg (pfmll_to_fml pfml1 runtime modul)
  | PAnd (pfml1, pfml2) -> And (pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul)
  | POr (pfml1, pfml2) -> Or (pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul)
  | PAX (str, pfml1, pel1) -> AX (str, pfmll_to_fml pfml1 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))
  | PEX (str, pfml1, pel1) -> EX (str, pfmll_to_fml pfml1 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))
  | PAF (str, pfml1, pel1) -> AF (str, pfmll_to_fml pfml1 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))
  | PEG (str, pfml1, pel1) -> EG (str, pfmll_to_fml pfml1 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))
  | PAR (str1, str2, pfml1, pfml2, pel1) -> AR (str1, str2, pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))
  | PEU (str1, str2, pfml1, pfml2, pel1) -> EU (str1, str2, pfmll_to_fml pfml1 runtime modul, pfmll_to_fml pfml2 runtime modul, State (evaluate (pexprl_to_expr pel1) [] runtime modul))


let pkripke_model_to_model (pkm:pkripke_model) runtime modul = 
    {
        transition = (ppatl_to_pattern (fst pkm.transition), List.map (fun (e1, e2) -> pexprl_to_expr e1, pexprl_to_expr e2) (snd pkm.transition));
        fairness = List.map (fun pfl -> pfmll_to_fml pfl runtime modul) pkm.fairness;
        properties = List.map (fun (str, pfmll) -> str, pfmll_to_fml pfmll runtime modul) pkm.properties;
    }

let pmoduls_to_runtime pmoduls pkripke_model start_modul =
    let dummy_kripke_model = {
        transition = (Pat_Symbol "", []);
        fairness = [];
        properties = [];
    } in
    let runtime = {
        moduls = Hashtbl.create 1;
        model = dummy_kripke_model;
    } in
    (* let moduls = Hashtbl.create 1 in *)
    let dep_graph = Dep.dep_graph_of_pmodul start_modul pmoduls in
    let rec modify_runtime dg =
        match dg with
        | Leaf mname -> 
            let m = Hashtbl.find pmoduls mname in 
            let modul = {
                imported = m.imported;
                vars = begin
                        let tmp_vars = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PExpr_loc (_, pel) -> Hashtbl.add tmp_vars str (evaluate (pexprl_to_expr pel) [] runtime mname)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_vars
                    end;
                functions = begin
                        let tmp_funs = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PFunction (_, ppatls, pel) -> Hashtbl.add tmp_funs str (List.map (fun ppatl -> ppatl_to_pattern ppatl) ppatls, pexprl_to_expr pel)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_funs
                    end;
            } in
            Hashtbl.add runtime.moduls mname modul
        | Node (mname, dgs) -> 
            List.iter (fun dg -> modify_runtime dg) dgs;
            let m = Hashtbl.find pmoduls mname in 
            let modul = {
                imported = m.imported;
                vars = begin
                        let tmp_vars = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PExpr_loc (_, pel) -> Hashtbl.add tmp_vars str (evaluate (pexprl_to_expr pel) [] runtime mname)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_vars
                    end;
                functions = begin
                        let tmp_funs = Hashtbl.create 1 in
                        Hashtbl.iter (fun str (_, ast) ->
                            match ast with
                            | PFunction (_, ppatls, pel) -> Hashtbl.add tmp_funs str (List.map (fun ppatl -> ppatl_to_pattern ppatl) ppatls, pexprl_to_expr pel)
                            | _ -> ()
                        ) m.psymbol_tbl;
                        tmp_funs
                    end;
            } in
            Hashtbl.add runtime.moduls mname modul in
        modify_runtime dep_graph;
        (* print_endline "initialized moduls in runtime"; *)
        runtime.model <- pkripke_model_to_model pkripke_model runtime start_modul;
        (* print_endline "initialized kripke model in runtime"; *)
        runtime



