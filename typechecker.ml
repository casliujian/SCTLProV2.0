open Ast
open Printf

exception Unify_error of ptyp * ptyp
exception Invalid_typepath of string
exception Invalid_pexpr_loc of pexpr_loc * string
exception Undefined_modul of string
exception Undefined_idenfier of string 


type env = (ptyp * ptyp) list

let rec merge_env env1 env2 = 
    let rec find_min_ptyp ptyp_list var = 
      match ptyp_list with
      | [] -> PTVar var
      | (PTVar v)::pts -> if v<var then find_min_ptyp pts v else find_min_ptyp pts var
      | pt::pts -> pt in
    let rec re_range_env env =
      match env with
      | [] -> []
      | (PTVar i, _)::env' -> 
        let pt_list = Pairs.find_all env (PTVar i) in
        let pt1 = find_min_ptyp pt_list i in
        let tmp_pt_list = ref [] in
        List.iter (fun pt -> if pt1<>pt then tmp_pt_list:=(pt, pt1)::(!tmp_pt_list)) pt_list;
        (PTVar i, pt1)::((!tmp_pt_list) @ (re_range_env (Pairs.remove_all env' (PTVar i))))
      | pt_pair ::env' -> pt_pair::(re_range_env env') in
    re_range_env (env1@env2)


let rec expand_udt pt modul moduls =
  match pt with
  | PTAray pt1 -> PTAray (expand_udt pt1 modul moduls)
  | PTLst pt1 -> PTLst (expand_udt pt1 modul moduls)
  | PTTuple pt_list -> PTTuple (List.map (fun pt->expand_udt pt modul moduls) pt_list)
  | PTRecord str_pt_list -> PTRecord (List.map (fun (str, pt) -> (str, expand_udt pt modul moduls)) str_pt_list)
  | PTArrow (pt1, pt2) -> PTArrow (expand_udt pt1 modul moduls, expand_udt pt2 modul moduls)
  | PTConstrs str_opt_list -> 
    PTConstrs (List.map (fun (str, opt) ->
        match opt with
        | None -> (str, None)
        | Some pt -> (str, Some (expand_udt pt modul moduls))
      ) str_opt_list) 
  | PTUdt (str, pt_list) -> 
    let pt1 = List.map (fun pt -> expand_udt pt modul moduls) pt_list in
    let strs = String.split_on_char '.' (String.trim str) in begin
      match strs with
      | [s] -> 
        if Hashtbl.mem moduls modul then begin
          let m = Hashtbl.find moduls modul in
          let tmp_pt = ref pt in
          let found = ref false in
          if Hashtbl.mem m.psymbol_tbl s then begin
            match (Hashtbl.find m.psymbol_tbl s) with
            | (UDT, PTyp pt) -> 
              tmp_pt := pt;
              (* print_endline ("found udt "^s); *)
              found := true;
              let index = ref 0 in
              List.iter (fun pt2 -> decr index; tmp_pt := replace_ptvar !tmp_pt !index pt2) pt1
            | _ -> ()
          end else
            List.iter (fun mname ->
              if not !found then begin
                let mi = Hashtbl.find moduls mname in
                match (Hashtbl.find mi.psymbol_tbl s) with
                | (UDT, PTyp pt) ->
                  tmp_pt := pt;
                  found := true;
                  let index = ref 0 in
                  List.iter (fun pt2 -> decr index; tmp_pt := replace_ptvar !tmp_pt !index pt2) pt1
                | _ -> ()
              end
            ) m.imported;

          (* let index = ref 0 in
          while !tmp_pt = PTVar 0 && !index < List.length m.imported do
            (try 
               tmp_pt := expand_udt pt (List.nth m.imported !index) moduls
             with Invalid_typepath _ -> ());
            incr index
          done; *)
          if not !found then begin
            (* Hashtbl.iter (fun sy def ->
              match def with
              | (UDT, _) -> print_string (sy^" ")
              | _ -> ()
            ) m.psymbol_tbl;
            print_endline ""; *)
            raise (Invalid_typepath (s^" was not defined."))
          end else
            !tmp_pt
        end else begin
          raise (Undefined_modul modul)
        end
      | [s1;s2] -> expand_udt (PTUdt (s2, pt1)) s1 moduls
      | _ -> raise (Invalid_typepath str)
    end
  | _ -> pt


let ptyp_of_env env var = 
  let rec ptyp_of_var ptyp_list var = 
    match ptyp_list with
    | [] -> PTVar var
    | (PTVar v)::pts -> ptyp_of_var (pts@(Pairs.find_all env (PTVar v))) v
    | pt :: pts -> pt in
  ptyp_of_var (Pairs.find_all env (PTVar var)) var

let rec apply_env_to_ptyp env ptyp = 
  (* let rec find_key_binding bindings key = 
    match bindings with
    | [] -> PTVar key
    | (PTVar ki, PTVar vi) :: bindings' -> if (key=ki)&&(ki>=vi) then PTVar vi else find_key_binding bindings' (key)
    | (PTVar ki, pt) :: bindings' -> if key=ki then pt else find_key_binding bindings' (key) 
    | _ :: bindings' -> find_key_binding bindings' (key)
  in *)
  match ptyp with
  | PTInt | PTFloat | PTBool | PTUnt | PTUdt _ -> ptyp
  | PTAray pt -> PTAray (apply_env_to_ptyp env pt)
  | PTLst pt -> PTLst (apply_env_to_ptyp env pt)
  | PTTuple pts -> PTTuple (List.map (fun a -> apply_env_to_ptyp env a) pts)
  | PTRecord str_ptyps -> PTRecord (List.map (fun (a,b) -> a, apply_env_to_ptyp env b) str_ptyps)
  | PTConstrs str_optyps -> 
    PTConstrs (List.map (fun (a, ob) -> 
        match ob with
        | None -> a, None
        | Some b -> a, Some (apply_env_to_ptyp env b)
      ) str_optyps)
  | PTVar vi -> 
        (* if vi = 18 then print_endline "calculating 18"; *)
       (* if vi = 21 then begin
        List.iter (fun (pt1, pt2)->print_endline ((Print.str_ptyp pt1)^","^(Print.str_ptyp pt2))) env;
        print_endline ("type of ptvar 21 is: "^(Print.str_ptyp (ptyp_of_env env (vi))))
      end;  *)
      let pt = (ptyp_of_env env (vi)) in
      if pt = ptyp then pt else apply_env_to_ptyp env pt
  | PTArrow (pt1, pt2) -> PTArrow (apply_env_to_ptyp env pt1, apply_env_to_ptyp env pt2)

let rec unify ptyp_list modul moduls = 
  match ptyp_list with
  | [] -> []
  | [ptyp] -> []
  | ptyp1 :: ptyp2 :: ptyps -> begin
      match ptyp1, ptyp2 with
      | PTInt, PTInt | PTFloat, PTFloat | PTBool, PTBool | PTUnt, PTUnt -> unify (ptyp2:: ptyps) modul moduls
      | PTVar vi1, PTVar vi2 -> 
        if vi1 = vi2 then 
          unify (ptyp2::ptyps) modul moduls
        else if vi1 < vi2 then
          let env = [(PTVar vi2, PTVar vi1)] in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
        else 
          let env = [(PTVar vi1, PTVar vi2)] in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | pt, PTVar vi | PTVar vi, pt -> 
        let env = [(PTVar vi, pt)] in
        merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | PTAray pt1, PTAray pt2 | PTLst pt1, PTLst pt2 -> 
        let env = unify [pt1;pt2] modul moduls in
        merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | PTTuple pts1, PTTuple pts2 -> 
        if List.length pts1 <> List.length pts2 then begin
          print_endline ("length of "^(Print.str_ptyp ptyp1)^" is not equal to "^(Print.str_ptyp ptyp2));
          raise (Unify_error (ptyp1, ptyp2))
        end else
          let env = List.fold_left (fun e (a1,a2) -> merge_env (unify [a1;a2] modul moduls) e) [] (List.combine pts1 pts2) in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | PTRecord str_pt_list1, PTRecord str_pt_list2 ->
        if List.length str_pt_list1 <> List.length str_pt_list2 then
          raise (Unify_error (ptyp1, ptyp2))
        else 
          let rec find_ptyp str_pt_list str =
            match str_pt_list with
            | [] -> PTVar 0
            | (s,pt)::str_pt_list' -> if s = str then pt else find_ptyp str_pt_list' str in
          let env = List.fold_left (fun e (str, pt) ->
              let pt2 = find_ptyp str_pt_list2 str in
              if pt2 = PTVar 0 then 
                raise (Unify_error (ptyp1, ptyp2))
              else
                merge_env e (unify [pt;pt2] modul moduls)
            ) [] str_pt_list1 in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | PTConstrs str_opt_list1, PTConstrs str_opt_list2 -> 
        if List.length str_opt_list1 <> List.length str_opt_list2 then
          raise (Unify_error (ptyp1, ptyp2))
        else 
          let rec find_ptyp str_pt_list str =
            match str_pt_list with
            | [] -> Some (PTVar 0)
            | (s,pt)::str_pt_list' -> if s = str then pt else find_ptyp str_pt_list' str in
          let env = List.fold_left (fun e (str, opt) ->
              let opt2 = find_ptyp str_opt_list2 str in
              match opt, opt2 with
              | None, None -> e
              | None, Some _ | Some _, None -> raise (Unify_error (ptyp1, ptyp2))
              | Some PTVar 0, _ | _, Some PTVar 0 -> raise (Unify_error (ptyp1, ptyp2))
              | Some pt1, Some pt2 -> e @ (unify [pt1; pt2] modul moduls)
            ) [] str_opt_list1 in
          merge_env env (unify (List.map (fun a -> apply_env_to_ptyp env a) (ptyp2::ptyps)) modul moduls)
      | PTUdt (str, ptyp_list), _ -> 
        (*let strs = String.split_on_char '.' (String.trim str) in*)
        (* let ptyp = ptyp_from_typepath str modul moduls in
           let index = ref (0) in
           let ptyp_concrete = List.fold_left (fun pt pt1 -> descr index; replace_ptvar pt index pt1) ptyp ptyp_list in *)
        let ptyp_concrete = expand_udt ptyp1 modul moduls in
        unify (ptyp_concrete::ptyp2::ptyps) modul moduls
      | _, PTUdt (str, ptyp_list) ->
        (*let strs = String.split_on_char '.' (String.trim str) in*)
        (* let ptyp = ptyp_from_typepath str modul moduls in
           let index = ref (0) in
           let ptyp_concrete = List.fold_left (fun pt pt1 -> descr index; replace_ptvar pt index pt1) ptyp ptyp_list in *)
        let ptyp_concrete = expand_udt ptyp2 modul moduls in
        unify (ptyp1::ptyp_concrete::ptyps) modul moduls
      | PTArrow (pt1, pt2), PTArrow (pt3, pt4) ->
        let env1 = unify [pt1; pt3] modul moduls in
        let env2 = unify [pt2; pt4] modul moduls in
        merge_env (merge_env env1 env2) (unify (ptyp2::ptyps) modul moduls)
      | _ ->
          print_endline ("error unifying types: "^(Print.str_ptyp ptyp1)^", "^(Print.str_ptyp ptyp2));  
          raise (Unify_error (ptyp1,ptyp2))
    end


type type_context = (string * ptyp) list

let rec find_ptyp str_ptyps str1 = 
  match str_ptyps with
  | [] -> PTVar 0
  | (str, ptyp) :: str_ptyps' -> if str1 = str then ptyp else find_ptyp str_ptyps' str1

let rec type_of_var str tctx = 
  match tctx with
  | [] -> PTVar 0
  | (s, pt) :: tctx' -> 
    if s=str then pt else type_of_var str tctx'
(* let pt = find_ptyp str_ptyps str in
   if pt = PTVar 0 then
    type_of_var str tctx'
   else 
    pt *)
let add_to_tctx str pt tctx = (str, pt) :: tctx

let rec type_of_str str modul moduls =
  try
    let pt = ref (PTVar 0) in
    let m = Hashtbl.find moduls modul in
    if Hashtbl.mem m.psymbol_tbl str then begin
      match (Hashtbl.find m.psymbol_tbl str) with
      | (Val, PExpr_loc (ptyp, pel)) -> pt := ptyp
      | (Var, PExpr_loc (ptyp, pel)) -> pt := ptyp
      | (Function, PFunction (ptyp, _, _)) -> pt := ptyp
      | _ -> ()
    end else begin
      List.iter (fun mname ->
          if Hashtbl.mem moduls mname then
            let m1 = Hashtbl.find moduls mname in
            if Hashtbl.mem m1.psymbol_tbl str then begin
              match (Hashtbl.find m1.psymbol_tbl str) with
              | (Val, PExpr_loc (ptyp, pel)) -> pt := ptyp
              | (Var, PExpr_loc (ptyp, pel)) -> pt := ptyp
              | (Function, PFunction (ptyp, _, _)) -> pt := ptyp
              | _ -> ()
            end
            else
              raise (Undefined_modul mname)
        ) m.imported
    end;
    if !pt = PTVar 0 then
      raise (Undefined_idenfier (str^" is not defined."))
    else 
      !pt
  with Not_found -> raise (Undefined_modul modul)


let rec check_ppat_type ppatl modul moduls =
  match ppatl.ppat with
  | PPat_Symbol str -> ([], add_to_tctx str ppatl.ptyp [])
  | PPat_Int _ -> let env1 = unify [PTInt; ppatl.ptyp] modul moduls in (env1, [])
  | PPat_Float _ -> let env1 = unify [PTFloat; ppatl.ptyp] modul moduls in (env1, [])
  | PPat_Unt -> let env1 = unify [PTUnt; ppatl.ptyp] modul moduls in (env1, [])
  | PPat_Aray ppatls -> 
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    begin
      match ppatls with
      | [] -> (!env0, !tctx0)
      | p::pl -> let env1 = unify [ppatl.ptyp; PTAray (p.ptyp)] modul moduls in (merge_env env1 !env0, !tctx0)
    end
  | PPat_Lst ppatls -> 
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    begin
      match ppatls with
      | [] -> (!env0, !tctx0)
      | p::pl -> let env1 = unify [ppatl.ptyp; PTLst (p.ptyp)] modul moduls in (merge_env env1 !env0, !tctx0)
    end
  | PPat_Lst_Cons (ppatl1, ppatl2) ->
    let env1, tctx1 = check_ppat_type ppatl1 modul moduls in
    let env2, tctx2 = check_ppat_type ppatl2 modul moduls in
    let env3 = unify [ppatl.ptyp; PTLst (ppatl1.ptyp); ppatl2.ptyp] modul moduls in
    (merge_env (merge_env env3 env2) env1, tctx1 @ tctx2)
  | PPat_Underline -> ([], [])
  | PPat_Tuple ppatls ->
    let env0 = ref [] 
    and tctx0 = ref [] in
    List.iter (fun ppatl -> 
        let env,tctx = check_ppat_type ppatl modul moduls in
        env0 := merge_env env !env0;
        tctx0 := tctx @ !tctx0
      ) ppatls;
    let env1 = unify [ppatl.ptyp; PTTuple (List.map (fun p->p.ptyp) ppatls)] modul moduls in 
    (merge_env env1 !env0, !tctx0)
  | PPat_Constr (str, oppatl) -> begin
      match oppatl with
      | None -> ([], [])
      | Some ppatl1 ->
        let env1, tctx1 = check_ppat_type ppatl1 modul moduls in
        (env1, tctx1)
    end


let rec ptyp_of_pexpr_path ptyp_expected str_list modul moduls =
  match str_list with
  | [] -> ptyp_expected
  | str::strs -> 
    if str = (String.capitalize_ascii str) then
      ptyp_of_pexpr_path ptyp_expected strs modul moduls
    else begin
      if ptyp_expected = PTVar 0 then
        ptyp_of_pexpr_path (type_of_str str modul moduls) strs modul moduls 
      else begin
        match ptyp_expected with
        | PTRecord str_ptyp_list -> begin
            match Pairs.find str_ptyp_list str with
            | None -> PTVar 0
            | Some ptyp -> ptyp_of_pexpr_path ptyp strs modul moduls
          end  
        | PTUdt _ -> 
          let pt = expand_udt ptyp_expected modul moduls in begin
            print_endline ("expanding udt "^(Print.str_ptyp ptyp_expected)^": "^(Print.str_ptyp pt));
            match pt with
            | PTRecord str_ptyp_list -> begin
                match Pairs.find str_ptyp_list str with
                | None -> print_endline ("can not find binding of "^str^" in record type "^(Print.str_ptyp pt));PTVar 0
                | Some ptyp -> ptyp_of_pexpr_path ptyp strs modul moduls
              end  
            | _ -> PTVar 0
          end
        | _ -> 
          (* print_endline ("ptyp_expected: "^(Print.str_ptyp ptyp_expected));  *)
          PTVar 0
      end
    end



let rec check_pel_type pel env tctx modul moduls = 
  match pel.pexpr with
  | PSymbol str_list -> begin
      match str_list with
      | [] -> raise (Invalid_pexpr_loc (pel, "not a valid expression."))
      | [str] -> 
        if str = (String.capitalize_ascii str) then
          raise (Invalid_pexpr_loc (pel, str^" is a module name, not an expression identifier."))
        else begin
          try
            if Pairs.key_exists tctx str then
              let pt = Pairs.get_value tctx str in
              let env1 = unify [pt; pel.ptyp] modul moduls in
              (merge_env env1 env, tctx)
            else begin
              let found = ref false in
              let tmp_env_tctx = ref ([], []) in
              let m = Hashtbl.find moduls modul in begin
                try 
                  match Hashtbl.find m.psymbol_tbl str with
                  | (Val, PExpr_loc (pt, pel1)) | (Var, PExpr_loc (pt, pel1)) ->
                    found := true;
                    let env1 = unify [pt;pel.ptyp; pel1.ptyp] modul moduls in 
                    tmp_env_tctx := (merge_env env1 env, tctx)
                  | _ -> raise (Undefined_idenfier ("not defined as a value: "^modul^"."^str))
                with Not_found -> raise (Undefined_idenfier (modul^"."^str))
              end;
              List.iter (fun mname ->
                let mi = Hashtbl.find moduls mname in
                try
                  match Hashtbl.find mi.psymbol_tbl str with
                  | (Val, PExpr_loc (pt, pel1)) | (Var, PExpr_loc (pt, pel1)) ->
                    found := true;
                    let env1 = unify [pt;pel.ptyp; pel1.ptyp] modul moduls in 
                    tmp_env_tctx := (merge_env env1 env, tctx)
                  | _ -> raise (Undefined_idenfier ("not defined as a value: "^mname^"."^str))
                with Not_found -> raise (Undefined_idenfier (mname^"."^str))
              ) m.imported;
              if not !found then
                raise (Undefined_idenfier (modul^"."^str))
              else
                !tmp_env_tctx
            end
            

            (* let pt = type_of_var str tctx in
            if pt = PTVar 0 then begin
              let m = Hashtbl.find moduls modul in
              try
                match (Hashtbl.find m.psymbol_tbl str) with
                | (Val, PExpr_loc (pt, pel1)) -> let env1 = unify [pt;pel.ptyp; pel1.ptyp] modul moduls in (merge_env env1 env, tctx)
                | (Var, PExpr_loc (pt, pel1)) -> let env1 = unify [pt;pel.ptyp; pel1.ptyp] modul moduls in (merge_env env1 env, tctx)
                | _ -> raise (Undefined_idenfier ("not defined as a value: "^modul^"."^str))
              with Not_found -> raise (Undefined_idenfier (modul^"."^str))
            end else begin
              let env1 = unify [pel.ptyp; pt] modul moduls in
              (merge_env env1 env, tctx)
            end *)
          with Not_found -> raise (Undefined_modul modul)
        end
      | str::strs -> 
        if str = (String.capitalize_ascii str) then
          let pt = ptyp_of_pexpr_path (PTVar 0) strs str moduls in
          if pt = PTVar 0 then 
            raise (Invalid_pexpr_loc (pel, "can not be typed"))
          else 
            let env1 = unify [pt; pel.ptyp] modul moduls in 
            (merge_env env1 env, tctx)
        else 
          let pt = type_of_var str tctx in
          if pt <> PTVar 0 then
            let pt1 = ptyp_of_pexpr_path pt strs modul moduls in
            if pt1 = PTVar 0 then
              (* raise (Invalid_pexpr_loc (pel, "can not be typed")) *)
              (env, tctx)
            else 
              let env1 = unify [pt1; pel.ptyp] modul moduls in
              (merge_env env1 env, tctx)
          else
            let pt1 = ptyp_of_pexpr_path (PTVar 0) str_list modul moduls in
            if pt1 = PTVar 0 then
              (* raise (Invalid_pexpr_loc (pel, "can not be typed")) *)
              (env, tctx)
            else 
              let env1 = unify [pt1; pel.ptyp] modul moduls in
              (merge_env env1 env, tctx)
          
    end
  (* | PLocal_Val (str, pel1) | PLocal_Var (str, pel1) -> 
    let env1, tctx1 = check_pel_type pel1 env tctx modul moduls in 
    (env1, add_to_tctx str pel1.ptyp tctx) *)
  | PLet (p, pel1) ->
    let env0, tctx0 = check_pel_type pel1 env tctx modul moduls in
    let env1, tctx1 = check_ppat_type p modul moduls in
    let env2 = unify [p.ptyp; pel1.ptyp] modul moduls in
    (merge_env (merge_env env0 env1) env2, tctx1 @ tctx)
  | PInt i -> let env1 = unify [pel.ptyp; PTInt] modul moduls in (merge_env env1 env, tctx)
  | PFloat f -> let env1 = unify [pel.ptyp; PTFloat] modul moduls in (merge_env env1 env, tctx)
  | PUnt -> let env1 = unify [pel.ptyp; PTUnt] modul moduls in (merge_env env1 env, tctx)
  | PAray pel_aray -> 
    let env1 = unify (List.map (fun (pel:pexpr_loc) -> pel.ptyp) (pel_aray)) modul moduls in
    let new_env = merge_env env1 env in
    (* List.iter (fun (pel:pexpr_loc) -> pel.ptyp <- apply_env_to_ptyp new_env pel.ptyp) pel_aray; *)
    let env2 = unify [pel.ptyp; PTAray ((List.hd pel_aray).ptyp)] modul moduls in 
    (merge_env env2 new_env, tctx)
  | PLst pel_list ->
    if List.length pel_list = 0 then
        (env, tctx)
    else
        let env1 = unify (List.map (fun (pel:pexpr_loc) -> pel.ptyp) pel_list) modul moduls in
        let new_env = merge_env env1 env in
        (* List.iter (fun (pel:pexpr_loc) -> pel.ptyp <- apply_env_to_ptyp new_env pel.ptyp) pel_list; *)
        let env2 = unify [pel.ptyp; PTLst ((List.hd pel_list).ptyp)] modul moduls in 
        (merge_env env2 new_env, tctx)
  | POp (op, pel_list) -> begin
      match op, pel_list with
      | "[]", [pel1; pel2] -> 
        let env1, _ = check_pel_type pel1 env tctx modul moduls  in
        (* let env2 = merge_env env1 env in *)
        let env3, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env4 = unify [pel.ptyp; PTAray (pel2.ptyp)] modul moduls in
        (merge_env env4 env3, tctx)
      | "::", [pel1; pel2] -> 
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel.ptyp; pel2.ptyp; PTLst (pel1.ptyp)] modul moduls in
        (merge_env env3 env2, tctx)
      | "@", [pel1; pel2] ->
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel.ptyp; pel2.ptyp; pel1.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "!", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTBool; pel1.ptyp; pel.ptyp] modul moduls in
        (merge_env env2 env1, tctx)
      | "&&", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "||", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "-", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTInt; pel1.ptyp; pel.ptyp] modul moduls in
        (merge_env env2 env1, tctx)
      | "-.", [pel1] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2 = unify [PTFloat; pel1.ptyp; pel.ptyp] modul moduls in
        (merge_env env2 env1, tctx)
      | "+", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "+.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "-", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "-.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "*", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTInt; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "*.", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTFloat; pel1.ptyp; pel2.ptyp; pel.ptyp] modul moduls in
        (merge_env env3 env2, tctx)
      | "=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | "!=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | "<", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | ">", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | "<=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | ">=", [pel1; pel2] ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
        let env4 = unify [PTBool; pel.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | str, _ ->(***reimplement this part***)
        (* print_endline ("checking type of function "^str); *)
        let ptf = type_of_str str modul moduls in
        let env0 = ref env in
        List.iter (fun pel ->
            let env, _ = check_pel_type pel !env0 tctx modul moduls in
            env0 := env
          ) pel_list;
        let pt1 = ref pel.ptyp in
        let rec construct_apply ptyps = 
          match ptyps with
          | [] -> raise (Invalid_pexpr_loc (pel, "not enough argument(s)."))
          | [pt] -> pt1 := pt; pt
          | pt::pts -> PTArrow (pt, construct_apply pts) in
        let env1 = unify [pel.ptyp; !pt1] modul moduls in
        let env2 = unify [ptf; construct_apply ((List.map (fun (pel:pexpr_loc)->pel.ptyp) pel_list)@[!pt1])] modul moduls in
        (merge_env (merge_env env1 env2) !env0, tctx)
    end
  | PBool b -> let env1 = unify [pel.ptyp; PTBool] modul moduls in (merge_env env1 env, tctx)
  | PTuple pel_list -> 
    let env0 = ref env in
    List.iter (fun pel ->
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
      ) pel_list;
    let env1 = unify [pel.ptyp; PTTuple (List.map (fun (pel:pexpr_loc) -> pel.ptyp) pel_list)] modul moduls in
    (merge_env env1 !env0, tctx)
  | PRecord str_pels ->
    let env0 = ref env in
    List.iter (fun (str, pel) ->
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
      ) str_pels;
    let env1 = unify [pel.ptyp; PTRecord (List.map (fun (str, (pel:pexpr_loc)) ->
        (str, pel.ptyp)
      ) str_pels)] modul moduls in
    (merge_env env1 !env0, tctx)
  | PIF (pel1, pel2, opel3) -> begin
      match opel3 with
      | None ->
        let env1,_ = check_pel_type pel1 env tctx modul moduls in
        let env2,_ = check_pel_type pel2 env1 tctx modul moduls in
        let env3 = unify [PTBool; pel1.ptyp] modul moduls in
        let env4 = unify [PTUnt; pel.ptyp; pel2.ptyp] modul moduls in
        (merge_env (merge_env env3 env4) env2, tctx)
      | Some pel3 ->
        let env1, _ = check_pel_type pel1 env tctx modul moduls in
        let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
        let env3, _ = check_pel_type pel3 env2 tctx modul moduls in
        let env4 = unify [PTBool; pel1.ptyp] modul moduls in
        let env5 = unify [pel.ptyp; pel2.ptyp; pel3.ptyp] modul moduls in
        (merge_env (merge_env env4 env5) env3, tctx)
    end
  | PWhile (pel1, pel2) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3 = unify [PTBool; pel1.ptyp] modul moduls in
    let env4 = unify [PTUnt; pel.ptyp; pel2.ptyp] modul moduls in
    (merge_env (merge_env env3 env4) env2, tctx)
  | PFor (str, pel1, pel2, pel3) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3, _ = check_pel_type pel3 env2 (add_to_tctx str pel1.ptyp tctx) modul moduls in
    let env4 = unify [PTInt; pel1.ptyp; pel2.ptyp] modul moduls in
    let env5 = unify [pel3.ptyp; pel.ptyp] modul moduls in
    (merge_env (merge_env env5 env4) env3, tctx)
  | PSeq pels ->
    if List.length pels = 0 then begin
      print_endline "PSeq expression can not contain 0 single expression";
      exit 1
    end;
    let env0 = ref env
    and tctx0 = ref tctx in
    List.iter (fun pel -> 
        let env, tctx = check_pel_type pel !env0 !tctx0 modul moduls in
        env0 := env;
        tctx0 := tctx
      ) pels;
    let env1 = unify [pel.ptyp; (List.hd (List.rev pels)).ptyp] modul moduls in
    (merge_env env1 !env0, tctx)
  | PAssign (pel1, pel2) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env2, _ = check_pel_type pel2 env1 tctx modul moduls in
    let env3 = unify [pel1.ptyp; pel2.ptyp] modul moduls in
    let env4 = unify [PTUnt; pel.ptyp] modul moduls in
    (merge_env (merge_env env3 env4) env2, tctx)
  | PMatch (pel1, ppatl_pel_list) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env0 = ref env1 in
    List.iter (fun (ppatl1, pel2) ->
        let env2, tctx2 = check_ppat_type ppatl1 modul moduls in
        env0 := merge_env env2 !env0;
        let env3, _ = check_pel_type pel2 !env0 (tctx2@tctx) modul moduls in
        let env4 = unify [pel1.ptyp; ppatl1.ptyp] modul moduls in
        let env5 = unify [pel.ptyp; pel2.ptyp] modul moduls in
        env0 := merge_env (merge_env env4 env5) env3
      ) ppatl_pel_list;
    (!env0, tctx)
  | PWith (pel1, str_pel_list) ->
    let env1, _ = check_pel_type pel1 env tctx modul moduls in
    let env0 = ref env1 in
    List.iter (fun (str, pel2) ->
        let env,_ = check_pel_type pel2 !env0 tctx modul moduls in
        env0 := env
      ) str_pel_list;
    (!env0, tctx)
  | PConstr _ -> (env, tctx)


let rec check_pformulal_type pfml tctx modul moduls =
  match pfml.pfml with
  | PAtomic (str, pel_list) -> 
    let env0 = ref [] in
    List.iter (fun ps ->
      match ps with
      | PSVar _ -> ()
      | PState pel -> 
        let env, _ = check_pel_type pel !env0 tctx modul moduls in
        env0 := env
    ) pel_list;
    !env0
  | PNeg pfml1 -> check_pformulal_type pfml1 tctx modul moduls
  | PAnd (pfml1, pfml2) -> merge_env (check_pformulal_type pfml1 tctx modul moduls) (check_pformulal_type pfml2 tctx modul moduls)
  | POr (pfml1, pfml2) -> merge_env (check_pformulal_type pfml1 tctx modul moduls) (check_pformulal_type pfml2 tctx modul moduls)
  | PAX (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.ptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env
  | PEX (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.ptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env
  | PAF (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.ptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env
  | PEG (x, pfml1, PState pel) -> 
    let env,_ = (check_pel_type pel [] tctx modul moduls) in
    let tctx1 = (x, pel.ptyp)::tctx in
    merge_env (check_pformulal_type pfml1 tctx1 modul moduls) env
  | PAR (x,y, pfml1, pfml2, PState pel) -> 
    let env,_ = check_pel_type pel [] tctx modul moduls in
    let tctx1 = (x, pel.ptyp)::tctx 
    and tctx2 = (y, pel.ptyp)::tctx in
    merge_env (merge_env (check_pformulal_type pfml1 tctx1 modul moduls) (check_pformulal_type pfml2 tctx2 modul moduls)) env
  | PEU (x,y, pfml1, pfml2, PState pel) -> 
    let env,_ = check_pel_type pel [] tctx modul moduls in
    let tctx1 = (x, pel.ptyp)::tctx 
    and tctx2 = (y, pel.ptyp)::tctx in
    merge_env (merge_env (check_pformulal_type pfml1 tctx1 modul moduls) (check_pformulal_type pfml2 tctx2 modul moduls)) env
  | _ -> []


let rec apply_env_to_ppatl env ppatl = 
  ppatl.ptyp <- apply_env_to_ptyp env ppatl.ptyp;
  match ppatl.ppat with
  | PPat_Aray ppatl1 -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl1
  | PPat_Lst ppatl1 -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl1
  | PPat_Lst_Cons (ppatl1, ppatl2) -> apply_env_to_ppatl env ppatl1; apply_env_to_ppatl env ppatl2
  | PPat_Tuple ppatl_list -> List.iter (fun ppatl -> apply_env_to_ppatl env ppatl) ppatl_list
  | PPat_Constr (str, oppatl) -> begin
      match oppatl with
      | None -> ()
      | Some ppatl1 -> apply_env_to_ppatl env ppatl1
    end
  | _ -> ()

let rec apply_env_to_pel env (pel:pexpr_loc) = 
  pel.ptyp <- apply_env_to_ptyp env pel.ptyp;
  match pel.pexpr with
  | PLet (ppatl, pel1) ->
    apply_env_to_ppatl env ppatl;
    apply_env_to_pel env pel1
  | PAray (pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PLst (pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | POp (op, pel_list) -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PTuple pel_list -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PRecord str_pel_list -> List.iter (fun (str,pel) -> apply_env_to_pel env pel) str_pel_list
  | PIF (pel1, pel2, opel3) -> begin
      match opel3 with
      | None -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
      | Some pel3 -> apply_env_to_pel env pel1; apply_env_to_pel env pel2; apply_env_to_pel env pel3
    end
  | PWhile (pel1, pel2) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
  | PFor (str, pel1, pel2, pel3) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2; apply_env_to_pel env pel3
  | PSeq pel_list -> List.iter (fun pel->apply_env_to_pel env pel) pel_list
  | PAssign (pel1, pel2) -> apply_env_to_pel env pel1; apply_env_to_pel env pel2
  | PMatch (pel1, ppatl_pel_list) -> 
    apply_env_to_pel env pel1; 
    List.iter (fun (ppatl, pel) -> apply_env_to_pel env pel; apply_env_to_ppatl env ppatl) ppatl_pel_list
  | PWith (pel1, str_pel_list) ->
    apply_env_to_pel env pel1; 
    List.iter (fun (str, pel) -> apply_env_to_pel env pel) str_pel_list
  | PConstr (PConstr_compound (str, pel1)) -> apply_env_to_pel env pel1
  | _ -> ()

let rec apply_env_to_pformulal env pfml =
  match pfml.pfml with
  | PAtomic (str, pel_list) -> 
      List.iter (fun ps->
        match ps with
        | PSVar _ -> ()
        | PState pel -> apply_env_to_pel env pel
      ) pel_list
  | PNeg pfml1 -> apply_env_to_pformulal env pfml1
  | PAnd (pfml1, pfml2) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2
  | POr (pfml1, pfml2) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2
  | PAX (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PEX (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PAF (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PEG (_, pfml1, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pel env pel
  | PAR (_,_, pfml1, pfml2, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2; apply_env_to_pel env pel
  | PEU (_,_, pfml1, pfml2, PState pel) -> apply_env_to_pformulal env pfml1; apply_env_to_pformulal env pfml2; apply_env_to_pel env pel
  | _ -> ()

let check_modul modul moduls = 
  if Hashtbl.mem moduls modul then begin
    let m = Hashtbl.find moduls modul in
    Hashtbl.iter (fun str kind_ast -> 
      match kind_ast with
      | (Val, PExpr_loc (ptyp, pel)) -> 
        let env,_ = check_pel_type pel [] [] modul moduls in
        let env1 = merge_env (unify [ptyp; pel.ptyp] modul moduls) env in
        let ptyp1 = apply_env_to_ptyp env1 ptyp in
        apply_env_to_pel env1 pel;
        Hashtbl.replace m.psymbol_tbl str (Val, PExpr_loc (ptyp1, pel))
        (* print_endline ("type check value "^str^" complete.") *)
      | (Var, PExpr_loc (ptyp, pel)) -> 
        let env,_ = check_pel_type pel [] [] modul moduls in
        let env1 = merge_env (unify [ptyp; pel.ptyp] modul moduls) env in
        let ptyp1 = apply_env_to_ptyp env1 ptyp in
        apply_env_to_pel env1 pel;
        Hashtbl.replace m.psymbol_tbl str (Var, PExpr_loc (ptyp1, pel))
        (* print_endline ("type check variable "^str^" complete.") *)
      | (Function, PFunction (ptyp, ppatl_list, pel)) -> 
        (* print_endline ("type checking function "^str); *)
        let rec build_arrow ptyp_list ptyp1 = 
          match ptyp_list with
          | [] -> ptyp1
          | pt::pts -> PTArrow (pt, build_arrow pts ptyp1) in
        let env0 = ref []
        and tctx0 = ref [] in
        List.iter (fun ppatl->
          let env,tctx = check_ppat_type ppatl modul moduls in
          env0:=merge_env env !env0;
          tctx0:=tctx@(!tctx0)
        ) ppatl_list;
        let env1, tctx1 = check_pel_type pel !env0 !tctx0 modul moduls in
        let env2 = merge_env (unify [ptyp; build_arrow (List.map (fun ppatl->ppatl.ptyp) ppatl_list) pel.ptyp] modul moduls) env1 in
        List.iter (fun ppatl->apply_env_to_ppatl env2 ppatl) ppatl_list;
        apply_env_to_pel env2 pel;
        Hashtbl.replace m.psymbol_tbl str (Function, PFunction (apply_env_to_ptyp env2 ptyp, ppatl_list, pel))
        (* print_endline ("type check function "^str^" complete.") *)
      | _ -> ()
    ) m.psymbol_tbl;
     match m.pkripke_model with
    | None -> ()
    | Some kripke -> 
        (* print_endline ("type checking kripke model..."); *)
        let env1, tctx1 = check_ppat_type (fst kripke.transition) modul moduls in
        let nexts = snd kripke.transition in begin
          match nexts with
          | PCase case_nexts ->  
            let tmp_env = ref env1 in
            List.iter (fun (e1, e2) -> 
              let env1, _ = check_pel_type e1 !tmp_env tctx1 modul moduls in
              let env2, _ = check_pel_type e2 env1 tctx1 modul moduls in
              tmp_env := env2
            ) case_nexts;
            apply_env_to_ppatl !tmp_env (fst kripke.transition);
            List.iter (fun (e1, e2) ->
              apply_env_to_pel !tmp_env e1;
              apply_env_to_pel !tmp_env e2
            ) case_nexts;
          | PNo_case no_case_nexts ->
            let tmp_env,_ = check_pel_type no_case_nexts env1 tctx1 modul moduls in
            apply_env_to_ppatl tmp_env (fst kripke.transition);
            apply_env_to_pel tmp_env no_case_nexts
        end;
        List.iter (fun (str, pfml) -> 
          let env = check_pformulal_type pfml [] modul moduls in
          apply_env_to_pformulal env pfml
        ) kripke.properties
        (* print_endline ("type check kripke model complete.") *)
  end else 
    raise (Undefined_modul modul)
