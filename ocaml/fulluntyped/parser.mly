%{
open Syntax
let rec m_of_int = function
    | 0 -> MZero
    | n -> MSucc(m_of_int (n-1))
%}
%token IF THEN ELSE TRUE FALSE
%token SUCC PRED ISZERO
%token TIMESFLOAT
%token LAMBDA
%token LET IN
%token <string> TX X STRINGV
%token <int> INTV
%token <float> FLOATV
%token APOSTROPHE DQUOTE ARROW BANG BARGT BARRCURLY BARRSQUARE
%token COLON COLONCOLON COLONEQ COLONHASH COMMA DARROW DDARROW DOT
%token EOF EQ EQEQ EXISTS GT LT HASH
%token LCURLYBAR LEFTARROW LCURLY RCURLY LPAREN RPAREN LSQUARE RSQUARE LSQUAREBAR
%token SEMI SLASH STAR TRIANGLE USCORE VBAR
%start p
%type <Syntax.c list> p
%%

p         : EOF                                   { [] }
          | c SEMI p                              { $1::$3 }
c         : m                                     { Eval($1) }
          | X b                                   { Bind($1, $2) }
b         : SLASH                                 { BName }
          | EQ m                                  { BMAbb($2) }
m         : m_app                                 { $1 }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LAMBDA X DOT m                        { MAbs($2, $4) }
          | LET X EQ m IN m                       { MLet($2, $4, $6) }
m_app     : m_path                                { $1 }
          | m_app m_path                          { MApp($1, $2) }
          | TIMESFLOAT m_path m_path              { MTimesfloat($2, $3) }
          | SUCC m_path                           { MSucc($2) }
          | PRED m_path                           { MPred($2) }
          | ISZERO m_path                         { MIsZero($2) }
m_path    : m_path DOT X                          { MProj($1, $3) }
          | m_path DOT INTV                       { MProj($1, string_of_int $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m RPAREN                       { $2 }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | X                                     { MVar($1) }
          | LCURLY fls RCURLY                     { MRecord($2 1) }
          | FLOATV                                { MFloat($1) }
          | STRINGV                               { MString($1) }
          | INTV                                  { m_of_int $1 }
fls       :                                       { fun i -> [] }
          | fls_ne                                { $1 }
fls_ne    : fl                                    { fun i -> [$1 i] }
          | fl COMMA fls_ne                       { fun i -> ($1 i) :: ($3 (i+1)) }
fl        : X EQ m                                { fun i -> ($1, $3) }
          | m                                     { fun i -> (string_of_int i, $1) }
