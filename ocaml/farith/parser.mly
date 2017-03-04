%{
open Syntax
let rec m_of_int = function
    | 0 -> MZero
    | n -> MSucc(m_of_int (n-1))
%}
%token TRUE FALSE IF THEN ELSE BOOL
%token SUCC PRED ISZERO NAT
%token LAMBDA
%token LET IN
%token AS
%token ALL
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
          | TX b_t                                { Bind($1, $2) }
          | X b                                   { Bind($1, $2) }
b_t       :                                       { BTVar }
          | EQ t                                  { BTAbb($2) }
b         : COLON t                               { BVar($2) }
          | EQ m                                  { BMAbb($2, None) }
t         : t_arr                                 { $1 }
          | ALL TX DOT t                          { TAll($2,$4) }
t_arr     : t_a ARROW t_arr                       { TArr($1, $3) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
          | BOOL                                  { TBool }
          | NAT                                   { TNat }
m         : m_app                                 { $1 }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
          | LET X EQ m IN m                       { MLet($2, $4, $6) }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LAMBDA TX DOT m                       { MTAbs($2,$4) }
m_app     : m_as                                  { $1 }
          | m_app m_a                             { MApp($1, $2) }
          | SUCC m_a                              { MSucc($2) }
          | PRED m_a                              { MPred($2) }
          | ISZERO m_a                            { MIsZero($2) }
          | m_app LSQUARE t RSQUARE               { MTApp($1, $3) }
m_as      : m_a AS t                              { MAscribe($1, $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | INTV                                  { m_of_int $1 }
