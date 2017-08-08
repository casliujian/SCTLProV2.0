open Expr
open Formula
open Interp
open Printf

module State_key = struct
	type t = value
	let compare = Pervasives.compare
end;;
module State_set = Set.Make(State_key)


let next s runtime modul = 
	let model = runtime.model in 
	let ctx, _ = get_matched_pattern s [(fst model.transition, Int 0)] in
	let nexts = snd model.transition in
	let next_states = ref State_set.empty in
	List.iter (fun (e1, e2) -> 
		match evaluate e1 ctx runtime modul with
		| VBool true -> next_states := State_set.add (evaluate e2 ctx runtime modul) !next_states 
		| VBool false -> ()
		| _ -> printf "%s should evaluate to a boolean value" (str_expr e1); exit 1
	) nexts;
	if State_set.is_empty !next_states then
		next_states := State_set.singleton s;
	!next_states
	(* let sl = evaluate (snd model.transition) ctx runtime modul in
	match sl with
	| VLst vs -> State_set.of_list vs
	| _ -> printf "%s is not a list of values." (str_value sl); exit 1 *)

type fairs = (formula * State_set.t) list

type continuation = 
      Basic of bool
    | Cont of State_set.t * fairs * string * formula * continuation * continuation * ((string * (value)) list) * ((string * (value)) list)

exception Error_proving_atomic
exception Unable_to_prove

let rec list_conditional lst c f = 
	match lst with
	| [] -> c
	| elem :: lst' -> if f elem = c then list_conditional lst' c f else not c

let fresh_fairs fairs = 
    List.map (fun (e, ss) -> (e, State_set.empty)) fairs

let orig_fairs = ref []
let has_fairs = ref false

let fresh_fairs_modl runtime =
	let fairs = runtime.model.fairness in
	if fairs = [] then [] else
	(
		has_fairs := true;
		List.map (fun (e) -> (e, State_set.empty)) fairs
	)

(****************************)
(* let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10

let is_in_true_merge s levl modl = 
	try
		let bs = ia_to_bin s modl in
		Bdd.int_array_satisfy bs (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl modl = 
	let bs = ia_to_bin s modl in
	Bdd.int_array_satisfy bs (Hashtbl.find false_merge levl)

let add_to_true_merge s levl modl = 
	try
		let bss = Hashtbl.find true_merge levl 
		and bs = ia_to_bin s modl in
		Hashtbl.replace true_merge levl (Bdd.add_int_array bs bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let add_to_false_merge s levl modl = 
	try
		let bss = Hashtbl.find false_merge levl 
		and bs = ia_to_bin s modl in
		Hashtbl.replace false_merge levl (Bdd.add_int_array bs bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1
 *)
let true_merge = Hashtbl.create 10
let false_merge = Hashtbl.create 10

let is_in_true_merge s levl = 
	try
		State_set.mem s (Hashtbl.find true_merge levl)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1

let is_in_false_merge s levl = 
	State_set.mem s (Hashtbl.find false_merge levl)

let add_to_true_merge s levl = 
	try
		let bss = Hashtbl.find true_merge levl in
		Hashtbl.replace true_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding true merge: "^levl); exit 1
let add_to_false_merge s levl = 
	try
		let bss = Hashtbl.find false_merge levl in
		Hashtbl.replace false_merge levl (State_set.add s bss)
	with Not_found -> print_endline ("level not found in finding false merge: "^levl); exit 1

let add_true_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, (levl, s)::ts, fs)
	| _ -> cont

let add_false_to_cont levl s cont = 
	match cont with
	| Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, fs) -> Cont (gamma, fairs, cont_levl, fml, contl, contr, ts, (levl, s)::fs)
	| _ -> cont

(****************************)

	(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (State_set.empty)) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (State_set.empty)) sub_fml_tbl

(* let in_global_merge s level modl = 
	let bs = ia_to_bin s modl in
    let sts = Hashtbl.find merges level in Bdd.int_array_satisfy bs sts

let add_to_global_merge ss level modl = 
	let sts = Hashtbl.find merges level in
	Hashtbl.replace merges level (State_set.fold (fun elem b -> let bs = ia_to_bin elem modl in Bdd.add_int_array bs b) ss sts)
  *)   
let in_global_merge s level = 
	State_set.mem s (Hashtbl.find merges level)

let add_to_global_merge ss level = 
	let sts = Hashtbl.find merges level in
	Hashtbl.replace merges level (State_set.fold (fun elem b -> State_set.add elem b) ss sts)
    
let clear_global_merge level = 
	Hashtbl.replace merges level (State_set.empty)
let get_global_merge level = 
	Hashtbl.find merges level


let generate_EX_cont gamma fairs levl x fml next contl contr = 
    State_set.fold (fun elem b ->
        Cont (State_set.empty, fresh_fairs fairs, levl^"1", And (subst_s fml x (State elem), EG ("y", Top, State elem)), contl, b, [], [])) next contr

let generate_AX_cont gamma fairs levl x fml next contl contr = 
    State_set.fold (fun elem b ->
        Cont (State_set.empty, fresh_fairs fairs, levl^"1", Or (subst_s fml x (State elem), Neg (EG ("y", Top, State elem))), b, contr, [], [])) next contl

let generate_EG_cont gamma fairs level x fml s next contl contr =
	let level1 = level^"1" in
    let nested = State_set.fold 
        (fun elem b -> 
            Cont (State_set.add s gamma, fairs, level, EG(x, fml, State elem), contl, add_false_to_cont level elem b, [], [])) next contr in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), nested, contr, [], [])

let generate_AF_cont gamma fairs levl x fml s next contl contr =
	let level1 = levl^"1" in 
    let nested = State_set.fold
        (fun elem b ->
            Cont (State_set.add s gamma, fairs, levl, AF(x, fml, State elem), add_true_to_cont levl elem b, contr, [], [])) next contl in
	Cont (State_set.empty, fresh_fairs fairs, level1, subst_s fml x (State s), contl, nested, [], [])

let generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
	(*let mk_fair_contl s1 cl cr = Cont (State_set.empty, fresh_fairs, "-1", EG (SVar "e", Top, (State s1)), cl, cr) in *)
    let nested = State_set.fold
        (fun elem b -> 
            Cont (State_set.singleton s, fairs, levl, EU(x, y, fml1, fml2, State elem), contl, b, [], [])) next contr in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			Cont (State_set.empty, fresh_fairs, "-1", EG ("e", Top, (State s)), contl, contr, [], []),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s), 
			contl,
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s),
				nested,
				contr, 
				[], []),
			[], [])

let generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr = 
	let levl1 = levl^"1"
	and levl2 = levl^"2" in
	let fresh_fairs = (if !orig_fairs = [] then fresh_fairs fairs else !orig_fairs) in
    let nested = State_set.fold
        (fun elem b ->
			Cont (State_set.singleton s, fairs, levl, AR (x, y, fml1, fml2, State elem), b, contr, [], [])) next contl in
		if !has_fairs then 
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			Cont (State_set.empty, fresh_fairs, "-1", EG ("e", Top, (State s)), 
				contr, 
				contl,
				[], []),
			[], [])
		else
			Cont (State_set.empty, fresh_fairs, levl2, subst_s fml2 y (State s),
			Cont (State_set.empty, fresh_fairs, levl1, subst_s fml1 x (State s), 
				contl,
				nested,
				[], []),
			contr,
			[], [])

let prove_atomic s sl runtime modul =
	let args = List.map (fun st ->
		match st with
		| SVar _ -> raise Error_proving_atomic
		| State value -> value
	) sl in
	let pats, e1 = find_function s runtime modul in
    if List.length args <> List.length pats then 
        raise (Evaluation_error ("function "^s^" has "^(string_of_int (List.length pats))^" parameters, but is applied to "^(string_of_int (List.length args))^" arguments."))
    else begin
        let ctx0 = ref [] in
        for i = 0 to List.length args - 1 do
            let v1 = List.nth args i in
            let ctx1, _ = get_matched_pattern v1 [(List.nth pats i, e1)] in
            ctx0 := ctx1 @ !ctx0
        done;
        let result = evaluate e1 (!ctx0) runtime modul in
        match result with
        | VBool b -> b
        | _ -> raise (Error_proving_atomic)
    end

let rec satisfy_fair fml s runtime modul =
	prove_fairs (Cont(State_set.empty, [], "0", subst_s fml ("s") (State s), Basic true, Basic false, [], [])) runtime modul

(* and prove_atomic s sl modl = 
	match s with
	(* | "has_next" -> State_set.is_empty (next (get_array_from_state (List.hd sl)) modl.transitions modl.var_index_tbl) *)
	| _ -> (try (match apply_atomic (Hashtbl.find modl.atomic_tbl s) sl modl.var_index_tbl with
			| Top -> true
			| Bottom -> false
			| _ -> raise Error_proving_atomic) with Not_found -> print_endline ("Did not find atomic formula: "^s); exit 1) 
 *)
and prove_fairs cont runtime modul = 
    match cont with 
    | Basic b -> b
    | Cont (gamma, fairs, levl, fml, contl, contr, ts, fs) ->
		(
			List.iter (fun (a, b) -> if a<>"-1" then add_to_true_merge b a) ts;
			List.iter (fun (a, b) -> if a<>"-1" then add_to_false_merge b a) fs
		);
        begin
            match fml with
            | Top -> prove_fairs contl runtime modul
            | Bottom -> prove_fairs contr runtime modul
            | Atomic (s, sl) -> if prove_atomic s sl runtime modul then prove_fairs contl runtime modul else prove_fairs contr runtime modul
			| Neg (Atomic (s, sl)) -> if prove_atomic s sl runtime modul then prove_fairs contr runtime modul else prove_fairs contl runtime modul
            | Neg fml1 -> prove_fairs (Cont (gamma, fairs, levl^"1", fml1, contr, contl, [], [])) runtime modul
            | And (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1, 
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl, 
                                    contr, 
									[],[]), 
                                contr,
								[],[])) runtime modul
            | Or (fml1, fml2) -> 
                prove_fairs (Cont (State_set.empty, fresh_fairs fairs, levl^"1", fml1,
                                contl,
                                Cont (State_set.empty, fresh_fairs fairs, levl^"2", fml2,
                                    contl,
                                    contr, [],[]),[],[])) runtime modul
            | AX (x, fml1, State s) -> 
                let next = next s runtime modul in
                prove_fairs (generate_AX_cont gamma fairs levl x fml1 next contl contr) runtime modul
            | EX (x, fml1, State s) -> 
                let next = next s runtime modul in
                prove_fairs (generate_EX_cont gamma fairs levl x fml1 next contl contr) runtime modul
            | EG (x, fml1, State s) -> 
				if (levl <> "-1") && (is_in_true_merge s levl) then prove_fairs contl runtime modul else
				if (levl <> "-1") && (is_in_true_merge s levl) then prove_fairs contr runtime modul else 
                if State_set.mem s gamma 
                then  
                    let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
                    if is_fair = true then prove_fairs contl runtime modul else ((*print_endline "EG merge, but not fair";*) prove_fairs contr runtime modul)
                else
                    let next = next s runtime modul in
                    (*let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e (State s) modl then (e, State_set.add s ss) else (e,ss)) fairs in*)
					let fairs_new = List.map (fun (e, ss) -> 
						if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in

						(* if eval_with_array e s modl.var_index_tbl = (Const 1) then (e, State_set.add s gamma) else (e,ss)) fairs in *)
					(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
                    prove_fairs (generate_EG_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
            | AF (x, fml1, State s) -> 
				if is_in_true_merge s levl then prove_fairs contl runtime modul else
				if is_in_false_merge s levl then prove_fairs contr runtime modul else
				begin
					if State_set.mem s gamma
					then 
						let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair = true then prove_fairs contr runtime modul else (prove_fairs contl runtime modul)
					else 
						begin
							let next = next s runtime modul in
							let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s runtime modul then (e, State_set.add s gamma) else (e,ss)) fairs in
							(*List.iter (fun (e, ss) -> print_endline ((str_expr e)^"-->"^(string_of_int (State_set.cardinal ss)))) fairs_new;*)
							prove_fairs (generate_AF_cont gamma fairs_new levl x fml1 s next contl contr) runtime modul
						end
				end
            | EU (x, y, fml1, fml2, State s) -> 
            	(*if State_set.is_empty gamma 
					then clear_global_merge levl 
					else add_to_global_merge gamma levl modl;
					if in_global_merge s levl modl
					then
						let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair then prove_fairs contr modl else prove_fairs contl modl 
						(* prove_fairs contr modl *)
					else
						let next = next s modl.transitions modl.var_index_tbl in
						let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in
						prove_fairs (generate_EU_cont gamma fairs_new levl x y fml1 fml2 s next contl contr) modl*)
				 (
					if State_set.is_empty gamma 
					then clear_global_merge levl 
					else add_to_global_merge gamma levl;
					if in_global_merge s levl
					then
						prove_fairs contr runtime modul
					else
						let next = next s runtime modul in
						prove_fairs (generate_EU_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
				) 
            | AR (x, y, fml1, fml2, State s) ->
            	(*(
            		if State_set.is_empty gamma
					then clear_global_merge levl
					else add_to_global_merge gamma levl modl;
					(*print_endline ("AR merge size: "^(string_of_int (State_set.cardinal (Hashtbl.find merges levl))))*)
				);		
				if in_global_merge s levl modl
				then 
					let is_fair = list_conditional fairs true (fun (e, ss) -> State_set.mem s ss) in
						if is_fair then prove_fairs contl modl else prove_fairs contr modl
				else
					let next = next s modl.transitions modl.var_index_tbl in
					let fairs_new = List.map (fun (e, ss) -> if satisfy_fair e s modl then (e, State_set.add s gamma) else (e,ss)) fairs in
					prove_fairs (generate_AR_cont gamma fairs_new levl x y fml1 fml2 s next contl contr) modl*)
				 (
					(if State_set.is_empty gamma
					then clear_global_merge levl
					else add_to_global_merge gamma levl;
					(*print_endline ("AR merge size: "^(string_of_int (State_set.cardinal (Hashtbl.find merges levl))))*)
					);		
					if in_global_merge s levl
					then 
						prove_fairs contl runtime modul
					else
						let next = next s runtime modul in
						prove_fairs (generate_AR_cont gamma fairs levl x y fml1 fml2 s next contl contr) runtime modul
				) 
			| _ -> (print_endline ("Unable to prove: "^(str_fml fml)); raise Unable_to_prove)
        end

	let rec prove_model runtime modul = 
		orig_fairs := fresh_fairs_modl runtime;
		let spec_lst = runtime.model.properties in 
		let rec prove_lst lst = 
		match lst with
		| [] -> ()
		| (s, fml) :: lst' -> 
			((let nnf_fml = nnf fml in 
			print_endline (str_fml (nnf_fml));
			pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
			let b = (prove_fairs (Cont (State_set.empty, List.map (fun e -> (e, State_set.empty)) runtime.model.fairness, "1", (nnf_fml), Basic true, Basic false, [], [])) runtime modul) in
			 print_endline (s ^ ": " ^ (string_of_bool b)));
			 prove_lst lst') in prove_lst spec_lst