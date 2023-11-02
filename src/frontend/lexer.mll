{
  open Lexing
  open Parser
  let newline lexbuf =
    let p = lexbuf.Lexing.lex_curr_p in
    let q =
      { p with Lexing.
        pos_lnum = p.Lexing.pos_lnum+1 ;
        pos_bol = p.Lexing.pos_cnum }
    in
      lexbuf.Lexing.lex_curr_p <- q

  exception Lexical_error of string

  let unterminated_comment () =
    raise (Lexical_error "unterminated comment")


}

let name = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
let path = '.' '/' ['a'-'z' 'A'-'Z' '0'-'9' '_' '.' '-' '/']+ '.' 's' 'p'
let int = ['0'-'9'] ['0'-'9']*

(* Hard-coded in Symbols.ml ! Do not change. *)
let right_infix_char_first = ['+' '-' '*' '|' '&' '~']
let  left_infix_char_first = ['^']

let infix_char = right_infix_char_first | left_infix_char_first | ['<' '>']

let left_infix_symb = 
   left_infix_char_first  ( infix_char* | (['0'-'9']* infix_char+) )
let right_infix_symb = 
   right_infix_char_first ( infix_char* | (['0'-'9']* infix_char+) )

rule token = parse
| [' ' '\t']              { token lexbuf }
| '\n'                    { newline lexbuf ; token lexbuf }
| "(*" { comment lexbuf; token lexbuf }

| "!_" (name as i)    { BANG i }
| "&&"                { AND }
| "/\\"               { GAND }
| "\\/"               { GOR }
| "||"                { OR }
| "not"               { NOT }
| "True"              { TRUE }
| "False"             { FALSE }
| '"'                 { QUOTE }
| '<'                 { LANGLE }
| '>'                 { RANGLE }
| '['                 { LBRACKET }
| ']'                 { RBRACKET }
| '{'                 { LBRACE }
| '}'                 { RBRACE }
| '?'                 { QMARK }
| ','                 { COMMA }
| "!"                 { BANGU }
| '.'                 { DOT }
| '#'                 { SHARP }
| '$'                 { DOLLAR }
| ':'                 { COLON }
| ":="                { COLONEQ }
| ';'                 { SEMICOLON }
| '*'                 { STAR }
| '_'                 { UNDERSCORE }
| "//"                { SLASHSLASH }
| "/="                { SLASHEQUAL }
| "//="               { SLASHSLASHEQUAL }
| '/'                 { SLASH }
| "@/"                { ATSLASH }
| "="                 { EQ }
| "<>"                { NEQ }
| ">="                { GEQ }
| "<="                { LEQ }
| '('                 { LPAREN }
| ')'                 { RPAREN }
| '|'                 { PARALLEL }
| "->"                { ARROW }
| "<-"                { RARROW }
| "=>"                { DARROW }
| "<=>"               { DEQUIVARROW }
| "-"                 { MINUS }
| "@"                 { AT }
| '~'                 { TILDE }
| '+'                 { PLUS }
| '\''                { TICK }
| '%'                 { PERCENT }
| int as i            { INT (int_of_string i) }
| "if"                { IF }
| "then"              { THEN }
| "else"              { ELSE }
| "let"               { LET }
| "Let"               { LLET }
| "XOR"               { XOR }
| "by"                { BY }
| "in"                { IN }
| "out"               { OUT }
| "new"               { NEW }
| "try find"          { FIND }
| "such that"         { SUCHTHAT }
| "process"           { PROCESS }
| "abstract"          { ABSTRACT }
| "action"            { ACTION }
| "op"                { OP }
| "predicate"         { PREDICATE }
| "fun"               { FUN }
| "type"              { TYPE }
| "name"              { NAME }
| "mutable"           { MUTABLE }
| "system"            { SYSTEM }
| "set"               { SET }
| "hash"              { HASH }
| "aenc"              { AENC }
| "senc"              { SENC }
| "signature"         { SIGNATURE }
| "intro"             { INTRO }
| "destruct"          { DESTRUCT }
| "fa"                { FA }
| "cs"                { CS }
| "as"                { AS }
| "index"             { INDEX }
| "message"           { MESSAGE }
| "channel"           { CHANNEL }
| "boolean"           { BOOLEAN }
| "bool"              { BOOL }
| "timestamp"         { TIMESTAMP }
| "null"              { NULL }
| "seq"               { SEQ }
| "rnd"               { RND }
| "var"               { VAR }
| "return"            { RETURN }
| "oracle"            { ORACLE }
| "game"              { GAME }
| "with"              { WITH }
| "where"             { WHERE }
| "time"              { TIME }
| "diff"              { DIFF }
| "forall"            { FORALL }
| "exists"            { EXISTS }
| "Forall"            { UFORALL }
| "Exists"            { UEXISTS }
| "splitseq"          { SPLITSEQ }
| "constseq"          { CONSTSEQ }
| "memseq"            { MEMSEQ }
| "remember"          { REMEMBER }
| "dependent"         { DEPENDENT }
| "lemma"             { LEMMA }
| "theorem"           { THEOREM }
| "local"             { LOCAL }
| "global"            { GLOBAL }
| "equiv"             { EQUIV }
| "axiom"             { AXIOM }
| "Proof."            { PROOF }
| "hint"              { HINT }
| "Qed."              { QED }
| "Reset."            { RESET }
| "Abort."            { ABORT }
| "help"              { HELP }
| "cycle"             { CYCLE }
| "undo"              { UNDO }
| "try"               { TRY }
| "repeat"            { REPEAT }
| "assert"            { ASSERT }
| "localize"          { LOCALIZE }
| "have"              { HAVE }
| "reduce"            { REDUCE }
| "auto"              { AUTO }
| "simpl"             { SIMPL }
| "exn"               { EXN }
| "crypto"            { CRYPTO }
| "use"               { USE }
| "rewrite"           { REWRITE }
| "trans"             { TRANS }
| "fresh"             { FRESH } 
| "apply"             { APPLY }
| "revert"            { REVERT }
| "generalize"        { GENERALIZE }
| "induction"         { INDUCTION }
| "depends"           { DEPENDS }
| "clear"             { CLEAR }
| "ddh"               { DDH }
| "cdh"               { CDH }
| "gdh"               { GDH }
| "nosimpl"           { NOSIMPL }
| "rename"            { RENAME }
| "gprf"              { GPRF }
| "gcca"              { GCCA }
| "checkfail"         { CHECKFAIL }
| "include"           { INCLUDE }
| "smt"               { SMT }
| "print"             { PRINT }
| "search"            { SEARCH }
| path as n           { PATH n }
| name as n           { ID n }
| eof                 { EOF }

|  left_infix_symb as s { LEFTINFIXSYMB s  }
| right_infix_symb as s { RIGHTINFIXSYMB s }


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | "\n"        { new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
