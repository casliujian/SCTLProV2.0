open Ast
open Typechecker
open Dep
open Interp
open Printf
open Lexing

(* let moduls = Hashtbl.create 0 *)

(* let debug () = 
    let exiting = ref true in
    let rec loop () = 
        while !exiting do
            let str = read_line () in
            printf "parsing: %s\n" str;
            if str <> "exit" then 
                let lbuf = Lexing.from_string str in
                try 
                    Parser.debug Lexer.token lbuf    
                with _ -> 
                    let ep = lbuf.lex_curr_p in
                    printf "syntax error at line %d, column %d\n" ep.pos_lnum (ep.pos_cnum - ep.pos_bol)
            else 
                exiting := false
        done in
    loop () *)

(* let test () = 
    let cha = open_in "test.model" in
    let lbuf = Lexing.from_channel cha in
    try 
        let imported, psymbol_tbl, pkripke_model = Parser.program Lexer.token (lbuf) in
        let modul = {
            fname = "test.model";
            imported = imported;
            psymbol_tbl = psymbol_tbl;
            pkripke_model = pkripke_model;
        } in
        Hashtbl.add moduls "Test" modul;
        let origin_out = open_out "test.origin" 
        and typed_out = open_out "test.typed" in
        output_string origin_out (Print.str_modul modul);
        Hashtbl.add moduls "Test" modul;
        Typechecker.check_modul "Test" moduls;
        output_string typed_out (Print.str_modul (Hashtbl.find moduls "Test"));
        flush origin_out;
        flush typed_out
    with Parser.Error -> 
        let ep = lbuf.lex_curr_p in
        printf "syntax error at line %d, column %d\n" ep.pos_lnum (ep.pos_cnum - ep.pos_bol) *)


let parse_and_prove fnames ip = 
    let get_mname fname = 
        (* List.iter (fun str -> print_endline (":"^str^" ")) (String.split_on_char '.' (String.trim fname)); *)
        (
            let lfname = List.hd (List.rev (String.split_on_char '/' (String.trim fname))) in
            let mname = List.hd (String.split_on_char '.' lfname
        ) in
        (* print_endline ("mname: "^(String.capitalize_ascii mname)); *)
        String.capitalize_ascii mname) in
    let pmoduls = Hashtbl.create 1 in
    let opkripke = ref None in
    let start_pmodul = ref "" in
    List.iter (fun fname -> 
        let mname = get_mname fname in
        (* print_endline ("proving modul "^mname^" in "^fname); *)
        let cha = open_in fname in
        let lbuf = Lexing.from_channel (cha) in
        try
            let imported, psymbol_tbl, pkripke_model = Parser.program Lexer.token lbuf in 
            (* print_endline ("*****************parse module "^mname^" finished*****************"); *)
            begin
                match pkripke_model with
                | None -> ()
                | Some pk -> opkripke := Some pk; start_pmodul := mname
            end;
            let modul = {
                fname = fname;
                imported = imported;
                psymbol_tbl = psymbol_tbl;
                pkripke_model = pkripke_model;
            } in
            let origin_out = open_out (mname^".origin") in
            output_string origin_out (Print.str_modul modul);
            flush origin_out;
            Hashtbl.add pmoduls mname modul
        with Parser.Error -> 
            let ep = lbuf.lex_curr_p in
            printf "syntax error at line %d, column %d\n" ep.pos_lnum (ep.pos_cnum - ep.pos_bol)
    ) fnames;
    match !opkripke with
    | None -> print_endline "no kripke model was built, exit."; exit 1
    | Some pkripke -> 
        let dg = dep_graph_of_pmodul !start_pmodul pmoduls in 
        let rec typecheck dg moduls = 
            match dg with
            | Leaf mname -> 
                (try
                    Typechecker.check_modul mname moduls;
                    let out = open_out (mname^".typed") in
                    output_string out (Print.str_modul (Hashtbl.find moduls mname));
                    flush out
                with Invalid_pexpr_loc (pel, msg) ->
                    print_endline ("Error: "^msg);
                    print_endline (Print.str_pexprl pel);
                    exit 1)
            | Node (mname, dgs) -> 
                List.iter (fun dg -> typecheck dg moduls) dgs; 
                (try
                    Typechecker.check_modul mname moduls;
                    let out = open_out (mname^".typed") in
                    output_string out (Print.str_modul (Hashtbl.find moduls mname));
                    flush out
                with Invalid_pexpr_loc (pel, msg) ->
                    print_endline ("Error: "^msg);
                    print_endline (Print.str_pexprl pel);
                    exit 1) in
        typecheck dg pmoduls;
        let runtime = pmoduls_to_runtime pmoduls pkripke !start_pmodul in
        match ip with
        | "" -> Prover.prove_model runtime !start_pmodul
        | str -> Prover_visualization.prove_model runtime !start_pmodul str




let _ = 
    let flag = ref 2 in
    let files = ref [] in
    let vis_addr = ref "" in
    Arg.parse [
        (* "-test", Arg.Unit (fun () -> flag := 0), "\tparse test.model";
        "-debug", Arg.Unit (fun () -> flag := 1), "\tdebug the parser interactively"; *)
        "-prove", Arg.Rest (fun str -> 
            (* print_endline ("rest: "^str); *)
            (* files := String.split_on_char ' ' (String.trim str); *)
            files := !files @ [str];
            flag := 2
        ), "\tinput files";
        "-visualize_addr", Arg.String (fun s -> vis_addr := s), "\tIP address of the vmdv server";
    ] (fun s -> files := !files @ [s]) "";
    match !flag with
    (* | 0 -> test ()
    | 1 -> debug () *)
    | 2 -> parse_and_prove !files !vis_addr
    | _ -> print_endline "don't know what to do."

    