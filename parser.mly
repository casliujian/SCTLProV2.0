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
%token Import Datatype Vertical Value Let Match With Underline Model Next Property If Then Else For In While Do Done
%token LB1 RB1 LB2 RB2 LB3 RB3 Equal Non_Equal LT GT LE GE Comma Semicolon Dot DotDot Arrow EOF Add AddDot Minus MinusDot Mult MultDot
%token Negb Ando Oro And Or Neg LArrow Colon ColonColon Init Top Bottom AX EX AF EG AR EU True False Function Of State
%token TLst TFloat TAray TInt TBool TUnt

%start <(string list) * (Ast.psymbol_tbl) * ((Ast.pkripke_model) option)>program
 %start <unit>debug 

/*%left Semicolon*/
%left Or
%left And
%right Neg


%right ColonColon
%left Oro
%left Ando
%right Negb
%nonassoc LT LE GT GE
%nonassoc Equal Non_Equal
%left Add AddDot 
%left Minus MinusDot
%left Mult MultDot
%nonassoc NEGI NEGF
%right Arrow


%%

debug: declare EOF {}
    | Import UIden {print_endline ("imported "^$2)}
;


program: imported declars EOF  {!imported, symbol_tbl, None} 
    | imported declars kripke EOF  {!imported, symbol_tbl, !kripke_model}
;

imported:   {}
    | imported Import UIden {print_endline ("imported "^$3); imported := $3 :: !imported}
;
 /* %inline declars: list(declare) {}
;      */

declars: {}
    | declare declars {}
;

declare: Datatype id = Iden args = list(Iden) Equal t = type_def  {
        Hashtbl.add symbol_tbl id (UDT, PTyp (erase_type_args t args))
        } 
    | Value id = Iden ote = option(type_of_expr)  Equal e = expr_single  {
            match ote with
            | None -> Hashtbl.add symbol_tbl id (Val, PExpr_loc (PTVar (new_type_var ()), e))
            | Some pt -> Hashtbl.add symbol_tbl id (Val, PExpr_loc (pt, e))
        }
    | Function id = Iden ags = args otf = option(type_of_expr) Equal e = expr  {
        match otf with
        | None -> Hashtbl.add symbol_tbl id (Function, PFunction(PTVar (new_type_var ()), ags, e))
        | Some pt -> Hashtbl.add symbol_tbl id (Function, PFunction(pt, ags, e))}
;

type_of_expr: Colon typ {$2}
;

args: pattern {[$1]}
    | pattern args  {$1 :: $2}
;    

kripke: Model LB3 states Next p = pattern Equal nexts = transition_items fair = separated_list(Semicolon, formula) pl = list(property) RB3    {
            kripke_model := Some {
                transition = (p, nexts);
                fairness = fair;
                properties = pl;
            }
        } 
;

transition_items: e1 = expr_single Colon e2 = expr_single Semicolon {[(e1, e2)]}
    | e1 = expr_single Colon e2 = expr_single Semicolon transition_items {(e1, e2)::$5}
;

states: {[]}
    | State Iden Equal expr_single states {($2, $4)::$5}
;

property: Property id = Iden Equal fml = formula  {(id, fml)}
;

formula: Top {mk_pformula_loc PTop $startpos($1) $endpos($1)}
    | Bottom {mk_pformula_loc PBottom $startpos($1) $endpos($1)}
    | id = Iden el = list(expr_single) {mk_pformula_loc (PAtomic (id, el)) $startpos(id) $endpos(el)}
    | Neg formula   {mk_pformula_loc (PNeg $2) $startpos($1) $endpos($2)}
    | formula And formula   {mk_pformula_loc (PAnd ($1, $3)) $startpos($1) $endpos($3)}
    | formula Or formula    {mk_pformula_loc (POr ($1, $3)) $startpos($1) $endpos($3)}
    | AX LB1 id = Iden Comma f = formula Comma e = expr_single RB1 {mk_pformula_loc (PAX (id, f, e)) $startpos($1) $endpos($8)}
    | EX LB1 id = Iden Comma f = formula Comma e = expr_single RB1 {mk_pformula_loc (PEX (id, f, e)) $startpos($1) $endpos($8)}
    | AF LB1 id = Iden Comma f = formula Comma e = expr_single RB1 {mk_pformula_loc (PAF (id, f, e)) $startpos($1) $endpos($8)}
    | EG LB1 id = Iden Comma f = formula Comma e = expr_single RB1 {mk_pformula_loc (PEG (id, f, e)) $startpos($1) $endpos($8)}
    | AR LB1 id1 = Iden Comma id2 = Iden Comma f1 = formula Comma f2 = formula Comma e = expr_single RB1 {mk_pformula_loc (PAR (id1, id2, f1, f2, e)) $startpos($1) $endpos($12)}
    | EU LB1 id1 = Iden Comma id2 = Iden Comma f1 = formula Comma f2 = formula Comma e = expr_single RB1 {mk_pformula_loc (PEU (id1, id2, f1, f2, e)) $startpos($1) $endpos($12)}
;

constrs: c = constr {[c]}
     | constr Vertical constrs {$1 :: $3} 
; 

type_def: typ {$1}
    | constrs {PTConstrs $1}
;

constr: uid = UIden {print_endline ("found constr "^uid); (uid, None)}
     | uid = UIden t = typ {(uid, Some t)} 
; 

typ: TInt {PTInt} 
    | TBool {PTBool}
    | TFloat {PTFloat}
    | TUnt  {PTUnt}
    | TAray typ {PTAray ($2)}
    | TLst typ {PTLst ($2)}
    | Iden tl = list(typ) {PTUdt ($1, tl)}
    | LB1 tuple_typ RB1 {PTTuple $2}
    | record_typ {PTRecord $1}
    | typ Arrow typ {PTArrow ($1, $3)}
    | LB1 t = typ RB1   {t}
;

tuple_typ: typ Comma typ {[$1; $3]}
    | typ Comma tuple_typ {$1 :: $3}
;

record_typ: LB3 str_pts = nonempty_list(str_typ) RB3 {str_pts}
;

str_typ: Iden Colon typ Semicolon {($1, $3)}
;


expr: expr_single {$1}
    | e = expr_single Semicolon el = separated_nonempty_list(Semicolon, expr_single)    {
            mk_pexpr_loc (PSeq (e::el)) (PTVar (new_type_var())) $startpos(e) $endpos(el)
        }
;

expr_path: id = Iden {[id]}
    | id = Iden Dot expr_path {id::$3}
;

expr_single: expr_path {mk_pexpr_loc (PSymbol $1) (PTVar (new_type_var ())) $startpos($1) $endpos($1)}
    | UIden Dot expr_path {mk_pexpr_loc (PSymbol ($1::$3)) (PTVar (new_type_var ())) $startpos($1) $endpos($3)}
    | i = Int   {mk_pexpr_loc (PInt i) (PTInt) $startpos(i) $endpos(i)}
    | f = Float {mk_pexpr_loc (PFloat f) (PTFloat) $startpos(f) $endpos(f)}
    | LB1 RB1   {mk_pexpr_loc PUnt (PTUnt) $startpos($1) $endpos($2)}
    | LB2 Vertical el = expr_single_list Vertical RB2   {
            let ea = el in
            if List.length ea = 0 then
                mk_pexpr_loc (PAray ea) (PTAray (PTVar (new_type_var ()))) $startpos($1) $endpos($5)
            else begin
                let e0 = List.hd ea in
                mk_pexpr_loc (PAray ea) (PTAray e0.ptyp) $startpos($1) $endpos($5)
            end 
        }
    | LB2 el = expr_single_list RB2    {
            if List.length el = 0 then
                mk_pexpr_loc (PLst el) (PTLst (PTVar (new_type_var ()))) $startpos($1) $endpos($3)
            else begin
                let e0 = List.hd el in
                mk_pexpr_loc (PLst el) (PTLst e0.ptyp) $startpos($1) $endpos($3)
            end
        }
    | True  {mk_pexpr_loc (PBool true) (PTBool) $startpos($1) $endpos($1)}
    | False {mk_pexpr_loc (PBool false) (PTBool) $startpos($1) $endpos($1)}
    | LB1 e = expr Comma el = separated_nonempty_list(Comma, expr) RB1 {
            let elt = List.map (fun (e:pexpr_loc) -> e.ptyp) (e::el) in
            mk_pexpr_loc (PTuple (e::el)) ((PTTuple elt)) $startpos($1) $endpos($5)
        }
    | LB3 str_el = str_expr_list RB3 {
            let str_elt = List.map (fun (str, (pel:pexpr_loc)) -> (str, pel.ptyp)) str_el in
            mk_pexpr_loc (PRecord str_el) (PTRecord str_elt) $startpos($1) $endpos($3)
        }
    | Negb e = expr_single     {
            mk_pexpr_loc (POp ("!", [e])) PTBool $startpos($1) $endpos(e)
        }
    | e1 = expr_single Ando e2 = expr_single  {
            mk_pexpr_loc (POp ("&&", [e1; e2])) PTBool $startpos(e1) $endpos(e2) 
        }
    | e1 = expr_single Oro e2 = expr_single  {
            mk_pexpr_loc (POp ("||", [e1;e2])) PTBool $startpos(e1) $endpos(e2)
        }
    | Minus e = expr_single %prec NEGI {
            mk_pexpr_loc (POp ("-", [e])) PTInt $startpos($1) $endpos(e)
        }
    | MinusDot e = expr_single %prec NEGF {
            mk_pexpr_loc (POp ("-.", [e])) PTFloat $startpos($1) $endpos(e)
        }
    | e1 = expr_single Add e2 = expr_single {
            mk_pexpr_loc (POp ("+", [e1;e2])) PTInt $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single Minus e2 = expr_single {
            mk_pexpr_loc (POp ("-", [e1;e2])) PTInt $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single Mult e2 = expr_single {
            mk_pexpr_loc (POp ("*", [e1;e2])) PTInt $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single AddDot e2 = expr_single {
            mk_pexpr_loc (POp ("+.", [e1;e2])) PTFloat $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single MinusDot e2 = expr_single {
            mk_pexpr_loc (POp ("-.", [e1;e2])) PTFloat $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single MultDot e2 = expr_single {
            mk_pexpr_loc (POp ("*.", [e1;e2])) PTFloat $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single Equal e2 = expr_single {mk_pexpr_loc (POp ("=", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | e1 = expr_single Non_Equal e2 = expr_single {mk_pexpr_loc (POp ("!=", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | e1 = expr_single LT e2 = expr_single    {mk_pexpr_loc (POp ("<", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | e1 = expr_single GT e2 = expr_single    {mk_pexpr_loc (POp (">", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | e1 = expr_single LE e2 = expr_single    {mk_pexpr_loc (POp ("<=", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | e1 = expr_single GE e2 = expr_single    {mk_pexpr_loc (POp (">=", [e1;e2])) PTBool $startpos(e1) $endpos(e2)}
    | If e1 = expr_single Then e2 = expr oe = option(else_expr)   {
            match oe with
            | None -> begin
                    mk_pexpr_loc (PIF (e1, e2, None)) PTUnt $startpos($1) $endpos(oe)
                end
            | Some e3 -> begin
                    mk_pexpr_loc (PIF (e1, e2, oe)) e2.ptyp $startpos($1) $endpos(oe)
                end
        }
    | While e1 = expr_single Do e2 = expr Done {
            mk_pexpr_loc (PWhile (e1, e2)) (PTUnt) $startpos($1) $endpos($5)
        }
    | For str = Iden In LB2 e2 = expr_single DotDot e3 = expr_single RB2 Do e4 = expr Done {
            mk_pexpr_loc (PFor (str, e2, e3, e4)) (PTUnt) $startpos($1) $endpos($11)
        }
    | e1 = expr_single LArrow e2 = expr_single    {mk_pexpr_loc (PAssign (e1, e2)) (PTUnt) $startpos(e1) $endpos(e2)}
    | Match e1 = expr_single With pel = pattern_expr_list {mk_pexpr_loc (PMatch (e1, pel)) (PTVar (new_type_var ())) $startpos($1) $endpos(pel)}
    | e1 = expr_single With LB3 str_el = str_expr_list RB3    {mk_pexpr_loc (PWith (e1, str_el)) e1.ptyp $startpos(e1) $endpos($5)}
    | uid = UIden {mk_pexpr_loc (PConstr ((PConstr_basic uid))) (PTVar (new_type_var ())) $startpos(uid) $endpos(uid)}
    | uid = UIden e = expr_single {
            mk_pexpr_loc (PConstr ((PConstr_compound (uid, e)))) (PTVar (new_type_var ())) $startpos(uid) $endpos(e)
        }
    | id = Iden el = nonempty_list(expr_single) {
            mk_pexpr_loc (POp (id, el)) (PTVar (new_type_var ())) $startpos(id) $endpos(el)
        }
    | Let p = pattern Equal e = expr_single {mk_pexpr_loc (PLet (p, e)) PTUnt $startpos($1) $endpos(e)}
    | e1 = expr_single ColonColon e2 = expr_single {
            mk_pexpr_loc (POp ("::", [e1; e2])) e2.ptyp $startpos(e1) $endpos(e2)
        }
    | e1 = expr_single LB2 e2 = expr_single RB2 {
        let e:Ast.pexpr_loc = e1 in
        let et1 = e.ptyp in
        match et1 with
        | PTAray pt -> mk_pexpr_loc (POp ("[]", [e1; e2])) pt $startpos(e1) $endpos($4)
        | PTVar _ -> mk_pexpr_loc (POp ("[]", [e1; e2])) (PTVar (new_type_var ())) $startpos(e1) $endpos($4)
        | _ -> raise (Type_mismatch (e1, et1, (PTAray (PTVar (new_type_var())))))        
        }
    | LB1 expr_single RB1  {$2}
;

expr_single_list:   {[]}
    | expr_single   {[$1]}
    | expr_single Semicolon expr_single_list {$1::$3}
;

str_expr_list:  {[]}
    | Iden Equal expr_single Semicolon {[($1, $3)]}
    | str_expr_list Iden Equal expr_single Semicolon   {($2, $4) :: $1}
;

else_expr: Else expr    {$2}
;

pattern_expr_list: option(Vertical) pe = pattern_expr {[pe]}
    | pattern_expr_list Vertical pattern_expr   {$1 @ [$3]} 
;
pattern_expr: pattern Arrow expr    {($1, $3)}
;

pattern: id = Iden   {mk_ppat_loc (PPat_Symbol id) (PTVar (new_type_var())) $startpos(id) $endpos(id)}
    | i = Int   {mk_ppat_loc (PPat_Int i) PTInt $startpos(i) $endpos(i)}
    | f = Float {mk_ppat_loc (PPat_Float f) PTFloat $startpos(f) $endpos(f)}
    | LB1 RB1   {mk_ppat_loc (PPat_Unt) PTUnt $startpos($1) $endpos($2)}
    | LB2 Vertical pl = pattern_list  Vertical RB2 {
            match pl with
            | [] -> mk_ppat_loc (PPat_Aray []) (PTAray (PTVar (new_type_var()))) $startpos($1) $endpos($5)
            | p::pl' -> mk_ppat_loc (PPat_Aray (pl)) (PTAray p.ptyp) $startpos($1) $endpos($5)
        }
    | LB2 pl = pattern_list RB2   {
            match pl with
            | [] -> mk_ppat_loc (PPat_Lst []) (PTLst (PTVar (new_type_var()))) $startpos($1) $endpos($3)
            | p::pl' -> mk_ppat_loc (PPat_Lst pl) (PTLst p.ptyp) $startpos($1) $endpos($3)
        }
    | p1 = pattern ColonColon p2 = pattern    {mk_ppat_loc (PPat_Lst_Cons (p1, p2)) (p2.ptyp) $startpos(p1) $endpos(p2)}
    | Underline     {mk_ppat_loc PPat_Underline (PTVar (new_type_var())) $startpos($1) $endpos($1)}
    | LB1 p = pattern Comma pl = separated_nonempty_list(Comma, pattern) RB1   {mk_ppat_loc (PPat_Tuple (p::pl)) (PTTuple (List.map (fun pat -> pat.ptyp) (p::pl))) $startpos($1) $endpos($5)}
    | uid = UIden {mk_ppat_loc (PPat_Constr (uid, None)) (PTVar (new_type_var())) $startpos(uid) $endpos(uid)}
    | uid = UIden p = pattern  {mk_ppat_loc (PPat_Constr (uid, Some p)) (PTVar (new_type_var())) $startpos(uid) $endpos(p)}
    | LB1 pattern RB1   {$2}
;

pattern_list:   {[]}
    | pattern   {[$1]}
    | pattern Semicolon pattern_list {$1 :: $3}
;

%%