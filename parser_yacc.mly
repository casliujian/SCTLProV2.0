%{
    open Ast

    let imported = ref []
    let symbol_tbl:(Ast.psymbol_tbl) = Hashtbl.create 1
    let kripke_model = ref None
    let type_var = ref 0
    let new_type_var () = 
        incr type_var;
        !type_var

    let erase_type_args t args = 
        let tmp_t = ref t in
        let rec erase_type_args_i pt i = 
            match pt with
            | PTUdt (str, pts) -> 
                let a = List.nth args i in
                if a=str then
                    PTVar (-i-1)
                else 
                    PTUdt (str, List.map (fun pt -> erase_type_args_i pt i) pts) 
            | PTAray pt1 -> PTAray (erase_type_args_i pt1 i) 
            | PTLst pt1 -> PTLst (erase_type_args_i pt1 i)
            | PTTuple pts -> PTTuple (List.map (fun pt -> erase_type_args_i pt i) pts)
            | PTRecord str_pts -> PTRecord (List.map (fun (str, pt) -> (str, erase_type_args_i pt i)) str_pts)
            | _ -> pt
        in
        for i = 0 to (List.length args) do
            tmp_t := erase_type_args_i !tmp_t i
        done;
        !tmp_t
%}
%token <int>Int 
%token <float>Float
%token <string>Iden UIden
%token Import Datatype Vertical Val Var Match With Underline Model Transition Property If Then Else For In While Do Done
%token LB1 RB1 LB2 RB2 LB3 RB3 Equal Non_Equal LT GT LE GE Comma Semicolon Dot DotDot Arrow EOF Add AddDot Minus MinusDot Mult MultDot
%token Negb Ando Oro And Or Neg LArrow Colon ColonColon Init Top Bottom AX EX AF EG AR EU True False Function
%token TLst TFloat TAray TInt TBool TUnt

%type <(string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option)>program
%start program

/*%left Semicolon*/
/* %left Or
%left And
%right Neg

%nonassoc LArrow With
%right ColonColon
%left Oro
%left Ando
%right Negb
%nonassoc LT LE GT GE
%nonassoc Equal Non_Equal
%left Add AddDot 
%left Minus MinusDot

%left Mult MultDot
%right Arrow */

%nonassoc LArrow With
%right Arrow
%right ColonColon

%left And
%left Or
%right Neg

%nonassoc LT LE GT GE
%left Add Minus AddDot MinusDot
%left Mult MultDot
%left Ando 
%left Oro
%nonassoc Equal Non_Equal
%right Negb
%nonassoc NEGI NEGF
%left Dot

%%

program: declars EOF    {[], symbol_tbl, None}
    | declars kripke EOF {[], symbol_tbl, !kripke_model}
    | imported declars EOF  {!imported, symbol_tbl, None} 
    | imported declars kripke EOF  {!imported, symbol_tbl, !kripke_model}
;

imported:  Import UIden  {imported := $2 :: !imported}
    | imported Import UIden {imported := $3 :: !imported}
;
 /* %inline declars: list(declare) {}
;      */
declars:    {}
    /*| Datatype id = Iden Equal cl = constr_locs   {Hashtbl.add symbol_tbl id (UDT, PConstrs cl)}*/
    | declars Datatype Iden type_args Equal type_def  {
        Hashtbl.add symbol_tbl $3 (UDT, PTyp (erase_type_args $6 $4)); 
        print_endline ("declared udt "^$3)} 
    | declars Var Iden Equal expr_single  {
            Hashtbl.add symbol_tbl $3 (Var, PExpr_loc (PTVar (new_type_var ()), $5))
        }
    | declars Var Iden type_of_expr Equal expr_single  {
            Hashtbl.add symbol_tbl $3 (Var, PExpr_loc ($4, $6))
        }
    | declars Val Iden Equal expr_single  {
            Hashtbl.add symbol_tbl $3 (Val, PExpr_loc (PTVar (new_type_var ()), $5))
        }
    | declars Val Iden type_of_expr Equal expr_single  {
            Hashtbl.add symbol_tbl $3 (Val, PExpr_loc ($4, $6))
        }
    | declars Function Iden args Equal expr  {
          Hashtbl.add symbol_tbl $3 (Function, PFunction(PTVar (new_type_var ()), $4, $6))
        }
    | declars Function Iden args type_of_expr Equal expr  {
        Hashtbl.add symbol_tbl $3 (Function, PFunction($5, $4, $7))}
;

type_args: {[]}
  | Iden type_args {$1 :: $2}
;

type_of_expr: Colon typ {$2}
;

args: pattern {[$1]}
    | pattern args  {$1 :: $2}
;    

kripke: Model LB3 Init Equal expr Semicolon Transition pattern Equal expr Semicolon list_property RB3    {
        kripke_model := Some {
            init = $5;
            transition = ($8, $10);
            properties = $12;
        }
    } 
;

list_property: {[]}
  | property list_property {$1::$2}
;

property: Property Iden Equal formula  {($2, $4)}
;

formula: Top {mk_pformula_loc PTop (rhs_start_pos 1) (rhs_end_pos 1)}
    | Bottom {mk_pformula_loc PBottom (rhs_start_pos 1) (rhs_end_pos 1)}
    | Iden list_expr {mk_pformula_loc (PAtomic ($1, $2)) (rhs_start_pos 1) (rhs_end_pos 2)}
    | Neg formula   {mk_pformula_loc (PNeg $2) (rhs_start_pos 1) (rhs_end_pos 2)}
    | formula And formula   {mk_pformula_loc (PAnd ($1, $3)) (rhs_start_pos 1) (rhs_end_pos 3)}
    | formula Or formula    {mk_pformula_loc (POr ($1, $3)) (rhs_start_pos 1) (rhs_end_pos 3)}
    | AX LB1 Iden Comma formula Comma expr RB1 {mk_pformula_loc (PAX ($3, $5, $7)) (rhs_start_pos 1) (rhs_end_pos 8)}
    | EX LB1 Iden Comma formula Comma expr RB1 {mk_pformula_loc (PEX ($3, $5, $7)) (rhs_start_pos 1) (rhs_end_pos 8)}
    | AF LB1 Iden Comma formula Comma expr RB1 {mk_pformula_loc (PAF ($3, $5, $7)) (rhs_start_pos 1) (rhs_end_pos 8)}
    | EG LB1 Iden Comma formula Comma expr RB1 {mk_pformula_loc (PEG ($3, $5, $7)) (rhs_start_pos 1) (rhs_end_pos 8)}
    | AR LB1 Iden Comma Iden Comma formula Comma formula Comma expr RB1 {mk_pformula_loc (PAR ($3, $5, $7, $9, $11)) (rhs_start_pos 1) (rhs_end_pos 12)}
    | EU LB1 Iden Comma Iden Comma formula Comma formula Comma expr RB1 {mk_pformula_loc (PEU ($3, $5, $7, $9, $11)) (rhs_start_pos 1) (rhs_end_pos 12)}
;
/*
args: pattern   {[$1]}
    | args pattern  {$2 :: $1}
;*/

/* constrs: option(Vertical) c = constr   {[c]}
        | cl = constrs Vertical c = constr   {cl @ [c]}
;  */
list_expr: {[]}
  | expr_single list_expr {$1::$2}
;

type_def: typ {$1}
    | constrs {PTConstrs $1}
;    

constrs: constr {[$1]}
    | constr Vertical constrs {$1 :: $3}
;

/* constrs: cl = separated_nonempty_list(Vertical, constr) {cl}
; */
constr: UIden {print_endline ("found constr "^$1); ($1, None)}
    | UIden typ {print_endline ("found constr with args "^$1); ($1, Some $2)}
; 

typ: TInt {PTInt} 
    | TBool {PTBool}
    | TFloat {PTFloat}
    | TUnt  {PTUnt}
    | TAray typ {PTAray ($2)}
    | TLst typ {PTLst ($2)}
    | Iden {PTUdt ($1, [])}
    | Iden udt_args {PTUdt ($1, $2)}
    /* | constrs {PTConstrs $1} */
    | LB1 tuple_typ RB1 {PTTuple $2}
    | record_typ {PTRecord $1}
    | typ Arrow typ {PTArrow ($1, $3)}
    | LB1 typ RB1   {$2}
;

udt_args: typ {[$1]}
  | LB1 comma_udt_args RB1 {$2}
;

comma_udt_args: typ Comma typ {[$1;$3]}
  | typ Comma comma_udt_args {$1::$3}
;

/* list_typ: {[]}
  | typ list_typ {$1::$2}
; */

tuple_typ: typ Comma typ {[$1; $3]}
    | typ Comma tuple_typ {$1 :: $3}
;

record_typ: LB3 str_typs RB3 {$2}
;

str_typs: str_typ {[$1]}
  | str_typ str_typs {$1::$2}
;

str_typ: Iden Colon typ Semicolon {($1, $3)}
;


expr: expr_single {$1}
    | expr_seq   {
            mk_pexpr_loc (PSeq ($1)) (PTVar (new_type_var())) (rhs_start_pos 1) (rhs_end_pos 1)
        }
;

expr_seq: expr_single Semicolon expr_single {[$1; $3]}
  | expr_single Semicolon expr_seq  {$1 :: $3}
;

expr_single: Iden {mk_pexpr_loc (PSymbol $1) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 1)}
    | Iden Dot expr_single     {
            let nt = PTVar (new_type_var ()) in
            mk_pexpr_loc (PDot (mk_pexpr_loc (PSymbol $1) nt (rhs_start_pos 1) (rhs_end_pos 1), $3)) nt (rhs_start_pos 1) (rhs_end_pos 3)
        }
    | UIden Dot expr_single {
            mk_pexpr_loc (PDot (mk_pexpr_loc (PSymbol $1) $3.ptyp (rhs_start_pos 1) (rhs_end_pos 1), $3)) $3.ptyp (rhs_start_pos 1) (rhs_end_pos 3)
        }
    | Int   {mk_pexpr_loc (PInt $1) (PTInt) (rhs_start_pos 1) (rhs_end_pos 1)}
    | Float {mk_pexpr_loc (PFloat $1) (PTFloat) (rhs_start_pos 1) (rhs_end_pos 1)}
    | LB1 RB1   {mk_pexpr_loc PUnt (PTUnt) (rhs_start_pos 1) (rhs_end_pos 2)}
    | LB2 Vertical expr_single_list Vertical RB2   {
            let ea = $3 in
            if List.length ea = 0 then
                mk_pexpr_loc (PAray ea) (PTAray (PTVar (new_type_var ()))) (rhs_start_pos 1) (rhs_end_pos 5)
            else begin
                let e0 = List.hd ea in
                mk_pexpr_loc (PAray ea) (PTAray e0.ptyp) (rhs_start_pos 1) (rhs_end_pos 5)
                (*match e0.ptyp with
                | None -> mk_pexpr_loc (PAray ea) None (rhs_start_pos 1) (rhs_end_pos 5)
                | Some t -> mk_pexpr_loc (PAray ea) (Some (PTAray (Some t))) (rhs_start_pos 1) (rhs_end_pos 5) *)
            end 
        }
    | LB2 expr_single_list RB2    {
            if List.length $2 = 0 then
                mk_pexpr_loc (PLst $2) (PTLst (PTVar (new_type_var ()))) (rhs_start_pos 1) (rhs_end_pos 3)
            else begin
                let e0 = List.hd $2 in
                mk_pexpr_loc (PLst $2) (PTLst e0.ptyp) (rhs_start_pos 1) (rhs_end_pos 3)
                (*match e0.ptyp with
                | None -> mk_pexpr_loc (PLst el) None (rhs_start_pos 1) (rhs_end_pos 3)
                | Some t -> mk_pexpr_loc (PLst el) (Some (PTLst (Some t))) (rhs_start_pos 1) (rhs_end_pos 3)*)
            end
        }
    | True  {mk_pexpr_loc (PBool true) (PTBool) (rhs_start_pos 1) (rhs_end_pos 1)}
    | False {mk_pexpr_loc (PBool false) (PTBool) (rhs_start_pos 1) (rhs_end_pos 1)}
    | LB1 expr_single Comma nonempty_single_expr_list_comma RB1 {
            let elt = List.map (fun (e:pexpr_loc) -> e.ptyp) ($2::$4) in
            mk_pexpr_loc (PTuple ($2::$4)) ((PTTuple elt)) (rhs_start_pos 1) (rhs_end_pos 5)
        }
    | LB3 str_expr_list RB3 {
            let str_elt = List.map (fun (str, (pel:pexpr_loc)) -> (str, pel.ptyp)) $2 in
            mk_pexpr_loc (PRecord $2) (PTRecord str_elt) (rhs_start_pos 1) (rhs_end_pos 3)
        }
    | Negb expr_single     {
            mk_pexpr_loc (PNegb $2) (PTBool) (rhs_start_pos 1) (rhs_end_pos 2)
            (*match e.ptyp with
            | None | Some PTBool -> 
                e.ptyp <- Some PTBool; 
                mk_pexpr_loc (PNegb e) (Some PTBool) (rhs_start_pos 1) $endpos(e)
            | Some t -> raise (Type_mismatch (e, t, PTBool))*)
        }
    | expr_single Ando expr_single  {
            mk_pexpr_loc (PAndo ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTBool | Some PTBool, None | Some PTBool, Some PTBool ->
                e1.ptyp <- Some PTBool;
                e2.ptyp <- Some PTBool;
                mk_pexpr_loc (PAndo (e1, e2)) (Some PTBool) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTBool)) 
            | Some t, Some PTBool -> raise (Type_mismatch (e1, t, PTBool))
            | None, Some t -> raise (Type_mismatch (e2, t, PTBool))
            | Some PTBool, Some t -> raise (Type_mismatch (e2, t, PTBool))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTBool))*)
        }
    | expr_single Oro expr_single  {
            mk_pexpr_loc (POro ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTBool | Some PTBool, None | Some PTBool, Some PTBool ->
                e1.ptyp <- Some PTBool;
                e2.ptyp <- Some PTBool;
                mk_pexpr_loc (POro (e1, e2)) (Some PTBool) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTBool)) 
            | Some t, Some PTBool -> raise ((Type_mismatch (e1, t, PTBool)))
            | None, Some t -> raise (Type_mismatch (e2, t, PTBool))
            | Some PTBool, Some t -> raise (Type_mismatch (e2, t, PTBool))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTBool))*)
        }
    | Minus expr_single %prec NEGI {
            mk_pexpr_loc (PNegi $2) (PTInt) (rhs_start_pos 1) (rhs_end_pos 2)
            (*match e.ptyp with
            | None | Some PTInt ->
                e.ptyp <- Some PTInt;
                mk_pexpr_loc (PNegi e) (Some PTInt) (rhs_start_pos 1) $endpos(e)
            | Some t -> raise (Type_mismatch (e, t, PTInt))*)
        }
    | MinusDot expr_single %prec NEGF {
            mk_pexpr_loc (PNegf $2) PTFloat (rhs_start_pos 1) (rhs_end_pos 2)
        }
    | expr_single Add expr_single {
            mk_pexpr_loc (PAdd ($1, $3)) (PTInt) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTInt | Some PTInt, None | Some PTInt, Some PTInt ->
                e1.ptyp <- Some PTInt;
                e2.ptyp <- Some PTInt;
                mk_pexpr_loc (PAdd (e1, e2)) (Some PTInt) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTInt)) 
            | Some t, Some PTInt -> raise (Type_mismatch (e1, t, PTInt))
            | None, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some PTInt, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTInt))*)
        }
    | expr_single Minus expr_single {
            mk_pexpr_loc (PMinus ($1, $3)) (PTInt) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTInt | Some PTInt, None | Some PTInt, Some PTInt ->
                e1.ptyp <- Some PTInt;
                e2.ptyp <- Some PTInt;
                mk_pexpr_loc (PMinus (e1, e2)) (Some PTInt) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTInt)) 
            | Some t, Some PTInt -> raise (Type_mismatch (e1, t, PTInt))
            | None, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some PTInt, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTInt))*)
        }
    | expr_single Mult expr_single {
            mk_pexpr_loc (PMult ($1, $3)) (PTInt) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTInt | Some PTInt, None | Some PTInt, Some PTInt ->
                e1.ptyp <- Some PTInt;
                e2.ptyp <- Some PTInt;
                mk_pexpr_loc (PMult (e1, e2)) (Some PTInt) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTInt)) 
            | Some t, Some PTInt -> raise (Type_mismatch (e1, t, PTInt))
            | None, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some PTInt, Some t -> raise (Type_mismatch (e2, t, PTInt))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTInt))*)
        }
    | expr_single AddDot expr_single {
            mk_pexpr_loc (PAddDot ($1, $3)) (PTFloat) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTFloat | Some PTFloat, None | Some PTFloat, Some PTFloat ->
                e1.ptyp <- Some PTFloat;
                e2.ptyp <- Some PTFloat;
                mk_pexpr_loc (PAddDot (e1, e2)) (Some PTFloat) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTFloat))
            | Some t, Some PTFloat -> raise (Type_mismatch (e1, t, PTFloat))
            | None, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some PTFloat, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTFloat))*)
        }
    | expr_single MinusDot expr_single {
            mk_pexpr_loc (PMinusDot ($1, $3)) (PTFloat) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTFloat | Some PTFloat, None | Some PTFloat, Some PTFloat ->
                e1.ptyp <- Some PTFloat;
                e2.ptyp <- Some PTFloat;
                mk_pexpr_loc (PMinusDot (e1, e2)) (Some PTFloat) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTFloat)) 
            | Some t, Some PTFloat -> raise (Type_mismatch (e1, t, PTFloat))
            | None, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some PTFloat, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTFloat))*)
        }
    | expr_single MultDot expr_single {
            mk_pexpr_loc (PMultDot ($1, $3)) (PTFloat) (rhs_start_pos 1) (rhs_end_pos 3)
            (*match e1.ptyp, e2.ptyp with
            | None, None | None, Some PTFloat | Some PTFloat, None | Some PTFloat, Some PTFloat ->
                e1.ptyp <- Some PTFloat;
                e2.ptyp <- Some PTFloat;
                mk_pexpr_loc (PMultDot (e1, e2)) (Some PTFloat) $startpos(e1) $endpos(e2)
            | Some t, None -> raise (Type_mismatch (e1, t, PTFloat))
            | Some t, Some PTFloat -> raise (Type_mismatch (e1, t, PTFloat))
            | None, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some PTFloat, Some t -> raise (Type_mismatch (e2, t, PTFloat))
            | Some t1, Some t2 -> raise (Type_mismatch (e1, t1, PTFloat))*)
        }
    | expr_single Equal expr_single {mk_pexpr_loc (PEqual ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | expr_single Non_Equal expr_single {mk_pexpr_loc (PNon_Equal ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | expr_single LT expr_single    {mk_pexpr_loc (PLT ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | expr_single GT expr_single    {mk_pexpr_loc (PGT ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | expr_single LE expr_single    {mk_pexpr_loc (PLE ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | expr_single GE expr_single    {mk_pexpr_loc (PGE ($1, $3)) (PTBool) (rhs_start_pos 1) (rhs_end_pos 3)}
    | If expr_single Then expr   {
            mk_pexpr_loc (PIF ($2, $4, None)) PTUnt (rhs_start_pos 1) (rhs_end_pos 4)
        }
    | If expr_single Then expr else_expr   {
            mk_pexpr_loc (PIF ($2, $4, Some $5)) $4.ptyp (rhs_start_pos 1) (rhs_end_pos 5)
        }
    | While expr_single Do expr Done {
            mk_pexpr_loc (PWhile ($2, $4)) (PTUnt) (rhs_start_pos 1) (rhs_end_pos 5)
        }
    | For Iden In LB2 expr_single DotDot expr_single RB2 Do expr Done {
            mk_pexpr_loc (PFor ($2, $5, $7, $10)) (PTUnt) (rhs_start_pos 1) (rhs_end_pos 11)
        }
    /*| e = expr Semicolon el = separated_nonempty_list(Semicolon, expr) {mk_pexpr_loc (PSeq (e::el)) None $startpos(e) $endpos(el)}*/
    /*| e1 = expr Semicolon e2 = expr   {mk_pexpr_loc (PSeq (e1, e2)) (e2.ptyp) $startpos(e1) $endpos(e2)}*/
    | expr_single LArrow expr_single    {mk_pexpr_loc (PAssign ($1, $3)) (PTUnt) (rhs_start_pos 1) (rhs_end_pos 3)}
    | Match expr_single With pattern_expr_list {mk_pexpr_loc (PMatch ($2, $4)) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 4)}
    | expr_single With LB3 str_expr_list RB3    {mk_pexpr_loc (PWith ($1, $4)) $1.ptyp (rhs_start_pos 1) (rhs_end_pos 5)}
    | UIden {mk_pexpr_loc (PConstr ((PConstr_basic $1))) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 1)}
    | UIden expr_single {
            mk_pexpr_loc (PConstr ((PConstr_compound ($1, $2)))) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 2)
        }
    | Iden nonempty_single_expr_list {
            mk_pexpr_loc (PApply ($1, $2)) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 2)
        }
    | Val Iden Equal expr_single   {mk_pexpr_loc (PLocal_Val ($2, $4)) (PTUnt) (rhs_start_pos 1) (rhs_end_pos 4)}
    | Var Iden Equal expr_single   {mk_pexpr_loc (PLocal_Var ($2, $4)) (PTUnt) (rhs_start_pos 1) (rhs_end_pos 4)}
    | expr_single LB2 expr_single RB2 {
        let e:Ast.pexpr_loc = $1 in
        let et1 = e.ptyp in
        match et1 with
        | PTAray pt -> mk_pexpr_loc (PAray_Field ($1, $3)) pt (rhs_start_pos 1) (rhs_end_pos 4)
        | PTVar _ -> mk_pexpr_loc (PAray_Field ($1, $3)) (PTVar (new_type_var ())) (rhs_start_pos 1) (rhs_end_pos 4)
        | _ -> raise (Type_mismatch ($1, et1, (PTAray (PTVar (new_type_var())))))        
        }
    | LB1 expr_single RB1  {$2}
;

nonempty_single_expr_list_comma: expr_single {[$1]}
  | expr_single Comma nonempty_single_expr_list_comma {$1::$3}
;

nonempty_single_expr_list: expr_single {[$1]}
  | expr_single nonempty_single_expr_list {$1::$2}
;

expr_single_list:   {[]}
    | expr_single   {[$1]}
    | expr_single Semicolon expr_single_list {$1::$3}
;

str_expr_list: Iden Equal expr Semicolon {[($1, $3)]}
    | str_expr_list Iden Equal expr Semicolon   {($2, $4) :: $1}
;
/*sel = separated_list(Semicolon, str_expr) {sel}*/
/*;*/

/*str_expr: Iden Equal expr   {($1, $3)}
;*/

else_expr: Else expr    {$2}
;

pattern_expr_list: Vertical pattern_expr {[$2]}
    | pattern_expr_list Vertical pattern_expr   {$1 @ [$3]} 
;
pattern_expr: pattern Arrow expr    {($1, $3)}
;

pattern: Iden   {mk_ppat_loc (PPat_Symbol $1) (PTVar (new_type_var())) (rhs_start_pos 1) (rhs_end_pos 1)}
    | Int   {mk_ppat_loc (PPat_Int $1) PTInt (rhs_start_pos 1) (rhs_end_pos 1)}
    | Float {mk_ppat_loc (PPat_Float $1) PTFloat (rhs_start_pos 1) (rhs_end_pos 1)}
    | LB1 RB1   {mk_ppat_loc (PPat_Unt) PTUnt (rhs_start_pos 1) (rhs_end_pos 2)}
    | LB2 Vertical Vertical RB2 {mk_ppat_loc (PPat_Aray []) (PTAray (PTVar (new_type_var()))) (rhs_start_pos 1) (rhs_end_pos 4)}
    | LB2 Vertical pattern_list  Vertical RB2 {
            mk_ppat_loc (PPat_Aray ($3)) (PTAray (List.hd $3).ptyp) (rhs_start_pos 1) (rhs_end_pos 5)
        }
    | LB2 RB2 {
        mk_ppat_loc (PPat_Lst []) (PTLst (PTVar (new_type_var()))) (rhs_start_pos 1) (rhs_end_pos 2)
      }
    | LB2 pattern_list RB2   {
            mk_ppat_loc (PPat_Lst $2) (PTLst (List.hd $2).ptyp) (rhs_start_pos 1) (rhs_end_pos 3)
        }
    | pattern ColonColon pattern    {mk_ppat_loc (PPat_Lst_Cons ($1, $3)) ($3.ptyp) (rhs_start_pos 1) (rhs_end_pos 3)}
    | Underline     {mk_ppat_loc PPat_Underline (PTVar (new_type_var())) (rhs_start_pos 1) (rhs_end_pos 1)}
    | LB1 pattern Comma nonempty_pattern_list_comma RB1   {mk_ppat_loc (PPat_Tuple ($2::$4)) (PTTuple (List.map (fun pat -> pat.ptyp) ($2::$4))) (rhs_start_pos 1) (rhs_end_pos 5)}
    /* | LB3 str_pl = str_pattern_list RB3   {mk_ppat_loc (PPat_Record str_pl) (rhs_start_pos 1) (rhs_end_pos 3)} */
    | UIden {mk_ppat_loc (PPat_Constr ($1, None)) (PTVar (new_type_var())) (rhs_start_pos 1) (rhs_end_pos 1)}
    | UIden pattern  {mk_ppat_loc (PPat_Constr ($1, Some $2)) (PTVar (new_type_var())) (rhs_start_pos 1) (rhs_end_pos 2)}
    | LB1 pattern RB1   {$2}
;

nonempty_pattern_list_comma: pattern {[$1]}
  | pattern Comma nonempty_pattern_list_comma {$1::$3}
;

pattern_list: pattern   {[$1]}
    | pattern Semicolon pattern_list {$1 :: $3}
;

/* str_pattern_list:    {[]}
    | Iden Equal pattern Semicolon  {[($1, $3)]}
    | str_pattern_list Iden Equal pattern Semicolon {($2, $4) :: $1}
; */
/*spl = separated_list(Semicolon, str_pattern) {spl}
;*/

/*str_pattern: Iden Equal pattern     {($1, $3)}
;*/
/*expr_aray:  {[||]}
    | expr  {[|$1|]}
    | expr Semicolon expr_aray  {Array.append [|$1|] $3}
;
expr_list:  {[]}
    | expr  {[$1]}
    | expr Semicolon expr_list  {$1 :: $3}
;*/
%%