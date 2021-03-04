%{
  module L  = Location
%}

%token <int> INT
%token <string> ID   /* general purpose identifier */
%token <string> PID  /* predicate identifier */
%token <string> BANG
%token AT PRED
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LANGLE RANGLE
%token AND OR NOT TRUE FALSE HAPPENS
%token EQ NEQ GEQ LEQ COMMA SEMICOLON COLON PLUS MINUS XOR STAR UNDERSCORE QMARK
%token LET IN IF THEN ELSE FIND SUCHTHAT
%token DIFF LEFT RIGHT NONE SEQ EXP
%token NEW OUT PARALLEL NULL
%token CHANNEL TERM PROCESS HASH AENC SENC SIGNATURE NAME ABSTRACT
%token MUTABLE SYSTEM SET
%token INIT INDEX MESSAGE BOOLEAN TIMESTAMP ARROW ASSIGN
%token EXISTS FORALL QUANTIF GOAL EQUIV DARROW DEQUIVARROW AXIOM
%token DOT SLASH BANGU
%token WITH ORACLE EXN
%token TRY CYCLE REPEAT NOSIMPL HELP DDH CHECKFAIL ASSERT USE REWRITE
%token BY INTRO AS DESTRUCT
%token PROOF QED UNDO ABORT
%token EOF

%nonassoc empty_else

%left XOR
%left EXP

%nonassoc ELSE
%nonassoc QUANTIF
%right ARROW
%right DARROW
%right DEQUIVARROW
%left OR
%left AND
/* %nonassoc NOT */

%nonassoc tac_prec

%left PLUS
%nonassoc REPEAT
%right SEMICOLON
%nonassoc TRY
%nonassoc NOSIMPL

%start declarations
%start top_formula
%start top_process
%start interactive
%type <Decl.declarations> declarations
%type <Theory.formula> top_formula
%type <Process.process> top_process
%type <Prover.parsed_input> interactive

%%

(* Ls *)
%inline loc(X):
| x=X {
    { L.pl_desc = x;
      L.pl_loc  = L.make $startpos $endpos;
    }
  }

(* Lists *)
%inline empty:
| { () }

%inline slist(X, S):
| l=separated_list(S, X) { l }

%inline slist1(X, S):
| l=separated_nonempty_list(S, X) { l }


(* Terms *)
lsymb:
| id=loc(ID) { id }

timestamp_i:
| id=lsymb terms=term_list               { Theory.App (id, terms) }
| PRED LPAREN ts=timestamp RPAREN        { Theory.Tpred ts }
| INIT                                   { Theory.Tinit }

timestamp:
| ts=loc(timestamp_i) { ts }

parens:
| LPAREN RPAREN { }

/* non-ambiguous term */
sterm_i:
| LPAREN t=term_i RPAREN                  { t }
| id=lsymb parens?                        { Theory.App (id, []) }
| id=lsymb parens? AT ts=timestamp        { Theory.AppAt (id,[],ts) }

| LANGLE t=term COMMA t0=term RANGLE
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "pair" in
      Theory.App (fsymb, [t;t0]) }

| INIT                                    { Theory.Tinit }

| PRED LPAREN t=term RPAREN               { Theory.Tpred t }
| DIFF LPAREN t=term COMMA t0=term RPAREN { Theory.Diff (t,t0) }
| SEQ LPAREN i=ids ARROW t=term RPAREN    { Theory.Seq (i,t) }

/* ambiguous term */
term_i:
| f=sterm_i                                  { f }
| id=lsymb terms=term_list1                  { Theory.App (id, terms) }
| id=lsymb terms=term_list1 AT ts=timestamp  { Theory.AppAt (id,terms,ts) }

| t=term XOR t0=term
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "xor" in
      Theory.App (fsymb,  [t;t0]) }

| t=term EXP t0=term
    { let loc = L.make $startpos $endpos in
      let fsymb = L.mk_loc loc "exp" in
      Theory.App (fsymb,  [t;t0])}
 
| IF b=formula THEN t=term t0=else_term
                                          { Theory.ITE (b,t,t0) }

| FIND is=indices SUCHTHAT b=formula IN t=term t0=else_term
                                          { Theory.Find (is,b,t,t0) }

/* non-ambiguous term */
%inline else_term:
| %prec empty_else   { let loc = L.make $startpos $endpos in
                       let fsymb = L.mk_loc loc "zero" in
                       L.mk_loc loc (Theory.App (fsymb, [])) }
| ELSE t=term       { t }

/* sterm: */
/* | t=loc(sterm_i) { t } */

term:
| t=loc(term_i) { t }

term_list:
|                                    { [] }
| LPAREN RPAREN                      { [] }
| LPAREN t=term terms=tm_list RPAREN { t::terms }

term_list1:
| LPAREN t=term terms=tm_list RPAREN { t::terms }

tm_list:
|                           { [] }
| COMMA tm=term tms=tm_list { tm::tms }

(* Facts, aka booleans *)

ord:
| EQ                             { `Eq }
| NEQ                            { `Neq }
| LEQ                            { `Leq }
| LANGLE                         { `Lt }
| GEQ                            { `Geq }
| RANGLE                         { `Gt }

kind:
| INDEX                          { Sorts.eindex }
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }
| TIMESTAMP                      { Sorts.etimestamp }

arg_list:
|                                         { [] }
| is=ids COLON k=kind                     { List.map (fun x -> x,k) is }
| is=ids COLON k=kind COMMA args=arg_list { List.map (fun x -> x,k) is @ args }

ids:
| id=lsymb                             { [id] }
| id=lsymb COMMA ids=ids               { id::ids }

top_formula:
| f=formula EOF                    { f }

/* non-ambiguous formula */
sformula_i:
| LPAREN f=formula_i RPAREN               { f }
| NOT f=sformula                          { Theory.Not (f) }
| FALSE                                   { Theory.False }
| TRUE                                    { Theory.True }

| HAPPENS LPAREN ts=slist1(timestamp,COMMA) RPAREN
                                 { Theory.Happens ts }

| DIFF LPAREN f=formula COMMA g=formula RPAREN
                                 { Theory.Diff (f,g) }

/* ambiguous formula */
formula_i:
| f=sformula_i                            { f }
| f=formula AND f0=formula                { Theory.And (f,f0) }
| f=formula OR f0=formula                 { Theory.Or (f,f0) }
| f=formula DARROW f0=formula             { Theory.Impl (f,f0) }
| f=term o=ord f0=term                    { Theory.Compare (o,f,f0) }

| f=formula DEQUIVARROW f0=formula
    { let loc = L.make $startpos $endpos in
      Theory.And (L.mk_loc loc (Theory.Impl (f,f0)),
                  L.mk_loc loc (Theory.Impl (f0,f))) }

| pid=loc(PID) terms=term_list   { Theory.App (pid, terms) }
| pid=loc(PID) terms=term_list AT ts=timestamp
                                 { Theory.AppAt (pid, terms, ts) }

| EXISTS LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.Exists (vs,f)  }
| FORALL LPAREN vs=arg_list RPAREN sep f=formula %prec QUANTIF
                                 { Theory.ForAll (vs,f)  }
| EXISTS id=lsymb COLON k=kind sep f=formula %prec QUANTIF
                                 { Theory.Exists ([id,k],f)  }
| FORALL id=lsymb COLON k=kind sep f=formula %prec QUANTIF
                                 { Theory.ForAll ([id,k],f)  }

sformula:
| f=loc(sformula_i) { f }

formula:
| f=loc(formula_i) { f }

sep:
|       {()}
| COMMA {()}

(* Processes *)

top_process:
| p=process EOF                    { p }

process_i:
| NULL                             { Process.Null }
| LPAREN ps=processes_i RPAREN     { ps }
| id=lsymb terms=term_list         { Process.Apply (id,terms) }
| id=lsymb COLON p=process         { Process.Alias (p,id) }
| NEW id=lsymb SEMICOLON p=process { Process.New (id,p) }
| IN LPAREN c=lsymb COMMA id=lsymb RPAREN p=process_cont
    { Process.In (c,id,p) }
| OUT LPAREN c=lsymb COMMA t=term RPAREN p=process_cont
    { Process.Out (c,t,p) }
| IF f=formula THEN p=process p0=else_process
    { Process.Exists ([],f,p,p0) }
| FIND is=indices SUCHTHAT f=formula IN p=process p0=else_process
    { Process.Exists (is,f,p,p0) }
| LET id=lsymb EQ t=term IN p=process
    { Process.Let (id,t,p) }
| id=lsymb terms=term_list ASSIGN t=term p=process_cont
    { let to_idx t = match L.unloc t with
        | Theory.App(x,[]) -> x
        | ti -> raise @@ Theory.Conv (L.loc t, Theory.Index_not_var ti)
      in
      let l = List.map to_idx terms in
      Process.Set (id,l,t,p) }
| s=loc(BANG) p=process { Process.Repl (s,p) }

process:
| p=loc(process_i) { p }

processes_i:
| p=process_i                             { p }
| p=process PARALLEL ps=loc(processes_i)  { Process.Parallel (p,ps) }

process_cont:
|                                { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| SEMICOLON p=process            { p }

else_process:
| %prec empty_else               { let loc = L.make $startpos $endpos in
                                   L.mk_loc loc Process.Null }
| ELSE p=process                 { p }

indices:
| id=lsymb                          { [id] }
| id=lsymb COMMA ids=indices        { id::ids }

opt_arg_list:
| LPAREN args=arg_list RPAREN    { args }
|                                { [] }

name_type:
| MESSAGE                        { 0 }
| INDEX ARROW t=name_type        { 1 + t }

msg_or_bool:
| MESSAGE                        { Sorts.emessage }
| BOOLEAN                        { Sorts.eboolean }

/* state_type:
| t=msg_or_bool                  { 0, t }
| INDEX ARROW t=state_type       { let n,k = t in n+1,k } */

msg_type:
| MESSAGE                        { 0 }
| MESSAGE ARROW t=msg_type       { 1 + t }

abs_type:
| t=msg_type                     { 0,t }
| INDEX ARROW t=abs_type         { let i,m = t in i+1,m }

index_arity:
|                                { 0 }
| LPAREN i=INT RPAREN            { i }

declaration_i:
| HASH e=lsymb a=index_arity
                          { Decl.Decl_hash (Some a, e, None) }
| HASH e=lsymb WITH ORACLE f=formula
                          { Decl.Decl_hash (None, e, Some f) }
| AENC e=lsymb COMMA d=lsymb COMMA p=lsymb
                          { Decl.Decl_aenc (e, d, p) }
| SENC e=lsymb COMMA d=lsymb
                          { Decl.Decl_senc (e, d) }
| SENC e=lsymb COMMA d=lsymb WITH h=lsymb
                          { Decl.Decl_senc_w_join_hash (e, d, h) }
| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
                          { Decl.Decl_sign (s, c, p, None) }
| SIGNATURE s=lsymb COMMA c=lsymb COMMA p=lsymb
  WITH ORACLE f=formula   { Decl.Decl_sign (s, c, p, Some f) }
| NAME e=lsymb COLON t=name_type
                          { Decl.Decl_name (e, t) }
| ABSTRACT e=lsymb COLON t=abs_type
                          { let index_arity,message_arity = t in
                            Decl.(Decl_abstract
                                    { name = e;
                                      index_arity=index_arity;
                                      message_arity=message_arity;}) }
| MUTABLE e=lsymb args=opt_arg_list COLON typ=msg_or_bool EQ t=term
                          { Decl.Decl_state (e, args, typ, t) }
| CHANNEL e=lsymb         { Decl.Decl_channel e }
| TERM e=lsymb args=opt_arg_list COLON typ=msg_or_bool EQ t=term
                          { Decl.Decl_macro (e, args, typ, t) }
| PROCESS e=lsymb args=opt_arg_list EQ p=process
                          { Decl.Decl_process (e, args, p) }
| AXIOM s=bsystem f=formula
                          { Decl.(Decl_axiom { gname = None;
                                               gsystem = s;
                                               gform = f; }) }
| AXIOM s=bsystem i=lsymb COLON f=formula
                          { Decl.(Decl_axiom { gname = Some i;
                                               gsystem = s;
                                               gform = f; }) }
| SYSTEM p=process
                          { Decl.(Decl_system { sname = None;
                                                sprocess = p}) }
| SYSTEM LBRACKET id=lsymb RBRACKET p=process
                          { Decl.(Decl_system { sname = Some id;
                                                sprocess = p}) }

declaration:
| ldecl=loc(declaration_i)                  { ldecl }

declaration_list:
| decl=declaration                        { [decl] }
| decl=declaration decls=declaration_list { decl :: decls }

declarations:
| decls=declaration_list DOT { decls }

tactic_param:
| t=term                    { TacticsArgs.Theory t }
| f=formula %prec tac_prec  { TacticsArgs.Theory f }
| i=INT                     { TacticsArgs.Int_parsed i }

tactic_params:
|                                       { [] }
| t=tactic_param                        { [t] }
| t=tactic_param COMMA ts=tactic_params { t::ts }

(*------------------------------------------------------------------*)
rw_mult:
| BANGU  { `Many }
| QMARK  { `Any }
|        { `Once }

rw_dir:
|       { `LeftToRight }
| MINUS { `RightToLeft }

rw_type:
| f=sformula      { `Form f }  

/* ad-hoc rule to allow hypothesis identifiers  */
| id=lsymb        { `Form (L.mk_loc (L.loc id) (Theory.App (id,[]))) }  

| SLASH id=lsymb  { `Expand id }

rw_param:
| m=rw_mult d=loc(rw_dir) t=rw_type  { TacticsArgs.{ rw_mult = m; 
                                                     rw_dir = d; 
                                                     rw_type = t; } }

rw_params:
| l=slist1(rw_param, empty) { l }

rw_in:
|                          { None }
| IN l=slist1(lsymb,COMMA) { Some (`Hyps l) }
| IN STAR                  { Some `All }

(*------------------------------------------------------------------*)
tac_errors:
|                         { [] }
| i=ID                    { [i] }
| i=ID COMMA t=tac_errors { i::t }

(*------------------------------------------------------------------*)
naming_pat:
| UNDERSCORE  { TacticsArgs.Unnamed }
| QMARK       { TacticsArgs.AnyName }
| id=ID       { TacticsArgs.Named id }

and_or_pat:
| LBRACKET s=simpl_pat          ips=slist(simpl_pat, empty)    RBRACKET
                    { TacticsArgs.And (s :: ips) }
| LBRACKET s=simpl_pat PARALLEL ips=slist(simpl_pat, PARALLEL) RBRACKET
                    { TacticsArgs.Or  (s :: ips) }
| LBRACKET RBRACKET { TacticsArgs.Split }

simpl_pat:
| n_ip=naming_pat  { TacticsArgs.SNamed n_ip }
| ao_ip=and_or_pat { TacticsArgs.SAndOr ao_ip }

intro_pat:
| l=loc(STAR)       { TacticsArgs.Star (L.loc l)}
| pat=simpl_pat     { TacticsArgs.Simpl pat }

intro_pat_list:
| l=slist1(intro_pat,empty) { l }

(*------------------------------------------------------------------*)
int:
|i=INT { i }

selector:
| l=slist1(int,COMMA) { l }

tac_formula:
| f=formula  %prec tac_prec { f }

as_ip:
| AS ip=simpl_pat { ip }

%inline sel_tac:
| s=selector COLON r=tac { (s,r) }

sel_tacs:
| l=slist1(sel_tac,PARALLEL) { l }

(*------------------------------------------------------------------*)
tac:
  | LPAREN t=tac RPAREN                { t }
  | l=tac SEMICOLON r=tac              { Tactics.AndThen [l;r] }
  | l=tac SEMICOLON LBRACKET sls=sel_tacs RBRACKET
                                       { Tactics.AndThenSel (l,sls) }
  | l=tac SEMICOLON sl=sel_tac %prec tac_prec
                                       { Tactics.AndThenSel (l,[sl]) }
  | BY t=tac %prec tac_prec            { Tactics.By t }
  | l=tac PLUS r=tac                   { Tactics.OrElse [l;r] }
  | TRY l=tac                          { Tactics.Try l }
  | REPEAT t=tac                       { Tactics.Repeat t }
  | id=ID t=tactic_params              { Tactics.Abstract (id,t) }
  (* A few special cases for tactics whose names are not parsed as ID
   * because they are reserved. *)
  | LEFT                               { Tactics.Abstract ("left",[]) }
  | RIGHT                              { Tactics.Abstract ("right",[]) }

  | INTRO p=intro_pat_list             { Tactics.Abstract
                                           ("intro",[TacticsArgs.IntroPat p]) }

  | t=tac DARROW p=intro_pat_list      { Tactics.AndThen
                                           [t;Tactics.Abstract
                                                ("intro",[TacticsArgs.IntroPat p])] }

  | DESTRUCT i=lsymb                   { Tactics.Abstract
                                           ("destruct",[TacticsArgs.String_name i]) }

  | DESTRUCT i=lsymb AS p=and_or_pat   { Tactics.Abstract
                                           ("destruct",[TacticsArgs.String_name i;
                                                        TacticsArgs.AndOrPat p]) }

  | EXISTS t=tactic_params             { Tactics.Abstract
                                          ("exists",t) }
  | NOSIMPL t=tac                      { Tactics.Modifier
                                          ("nosimpl", t) }
  | CYCLE i=INT                        { Tactics.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed i]) }
  | CYCLE MINUS i=INT                  { Tactics.Abstract
                                         ("cycle",[TacticsArgs.Int_parsed (-i)]) }
  | CHECKFAIL t=tac EXN ts=tac_errors  { Tactics.CheckFail
                                         (Tactics.tac_error_of_strings  ts,t) }
  | ASSERT p=tac_formula ip=as_ip?
    { let ip = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      Tactics.Abstract
        ("assert", TacticsArgs.Theory p::ip) }

  | USE i=lsymb ip=as_ip?
    { let ip = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      Tactics.Abstract ("use", ip @ [TacticsArgs.String_name i]) }

  | USE i=lsymb WITH t=tactic_params ip=as_ip?
    { let ip : TacticsArgs.parser_arg list = match ip with
        | None -> []
        | Some ip -> [TacticsArgs.SimplPat ip] in
      Tactics.Abstract ("use", ip @ [TacticsArgs.String_name i] @ t) }

  | REWRITE p=rw_params w=rw_in
    { Tactics.Abstract ("rewrite", [TacticsArgs.RewriteIn (p, w)]) }

  | DDH i1=lsymb COMMA i2=lsymb COMMA i3=lsymb  { Tactics.Abstract
                                          ("ddh",
                                           [TacticsArgs.String_name i1;
					                                  TacticsArgs.String_name i2;
					                                  TacticsArgs.String_name i3;
				                                   ]) }

  | HELP                               { Tactics.Abstract
                                          ("help",
                                           []) }

  | HELP i=lsymb                          { Tactics.Abstract
                                          ("help",
                                           [TacticsArgs.String_name i]) }

  | HELP h=help_tac
   { Tactics.Abstract ("help",[TacticsArgs.String_name h]) }

(* A few special cases for tactics whose names are not parsed as ID
 * because they are reserved. *)
help_tac_i:
| LEFT      { "left"}     
| RIGHT     { "right"}    
| EXISTS    { "exists"}    
| USE       { "use"}      
| REWRITE   { "rewrite"}  
| DDH       { "ddh"}      
| ASSERT    { "assert"}   
| DESTRUCT  { "destruct"} 
| INTRO     { "intro"} 

help_tac:
| l=loc(help_tac_i) { l }

qed:
| QED                                 { () }

abort:
| ABORT                               { () }


undo:
| UNDO i=INT DOT                      { i }

tactic:
| t=tac DOT                           { t }

equiv_item:
| t=term           { `Message t }
| f=formula        { `Formula f }

equiv:
| ei=equiv_item                 { [ei] }
| ei=equiv_item COMMA eis=equiv { ei::eis }

equiv_form:
| LBRACKET f=formula RBRACKET      { Prover.PReach f }
| e=equiv            { Prover.PEquiv e }
/* | LPAREN f=equiv_form RPAREN       { f } */
| f=equiv_form ARROW f0=equiv_form { Prover.PImpl (f,f0) }

args:
|                                         { [] }
| LPAREN vs0=arg_list RPAREN vs=args { vs0 @ vs }

system:
|                         { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET LEFT RBRACKET  { SystemExpr.(P_Single (P_Left default_system_name)) }
| LBRACKET RIGHT RBRACKET { SystemExpr.(P_Single (P_Right default_system_name)) }
| LBRACKET NONE  COMMA i=lsymb RBRACKET { SystemExpr.(P_SimplePair i) }
| LBRACKET LEFT  COMMA i=lsymb RBRACKET { SystemExpr.(P_Single (P_Left i)) }
| LBRACKET RIGHT COMMA i=lsymb RBRACKET { SystemExpr.(P_Single (P_Right i)) }

bsystem:
|                            { SystemExpr.(P_SimplePair default_system_name) }
| LBRACKET i=lsymb RBRACKET  { SystemExpr.(P_SimplePair i) }

single_system:
| LBRACKET LEFT RBRACKET  { SystemExpr.(P_Left default_system_name)}
| LBRACKET RIGHT RBRACKET { SystemExpr.(P_Right default_system_name)}
| LBRACKET LEFT  COMMA i=lsymb RBRACKET { SystemExpr.(P_Left i) }
| LBRACKET RIGHT COMMA i=lsymb RBRACKET { SystemExpr.(P_Right i)}

gname:
| i=lsymb    { P_named i }
| UNDERSCORE { P_unknown }

goal_i:
| GOAL s=system n=gname args=args COLON f=formula DOT
    { let f_i = Theory.ForAll (args, f) in
      let fa = L.mk_loc (L.loc f) f_i in
      Prover.Gm_goal (n, P_trace_goal (s, fa)) }

| EQUIV n=gname env=args COLON f=loc(equiv_form) DOT
                 { Prover.Gm_goal (n, P_equiv_goal (env, f)) }
| EQUIV n=gname DOT
                 { Prover.Gm_goal
                     (n, P_equiv_goal_process
                                   (SystemExpr.(P_Left  default_system_name),
			                              SystemExpr.(P_Right default_system_name))) }
| EQUIV b1=single_system b2=single_system n=gname DOT
                 { Prover.Gm_goal
                     (n, Prover.P_equiv_goal_process (b1, b2))}

| PROOF          { Prover.Gm_proof }

goal:
| goal=loc(goal_i) { goal }

option_param:
| TRUE  { Config.Param_bool true  }
| FALSE { Config.Param_bool false }
| n=ID  {
        if n = "true" then (Config.Param_bool true)
        else if n = "false" then (Config.Param_bool false)
        else Config.Param_string n   }
| i=INT { Config.Param_int i      }

set_option:
| SET n=ID EQ param=option_param DOT { (n, param) }

interactive :
| set=set_option     { Prover.ParsedSetOption set }
| decls=declarations { Prover.ParsedInputDescr decls }
| u=undo             { Prover.ParsedUndo u }
| tac=tactic         { Prover.ParsedTactic tac }
| qed                { Prover.ParsedQed }
| abort              { Prover.ParsedAbort }
| g=goal             { Prover.ParsedGoal g }
| EOF                { Prover.EOF }
