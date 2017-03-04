%{
open Syntax
let rec addbinders t = function
  | [] -> t
  | (tx,k)::rest -> TAbs(tx, k, addbinders t rest)

let rec m_of_int = function
  | 0 -> MZero
  | n -> MSucc(m_of_int (n-1))
%}
%token TRUE FALSE IF THEN ELSE BOOL
%token SUCC PRED ISZERO NAT
%token UNIT UUNIT
%token LAMBDA
%token LET IN
%token LETREC FIX
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
k         : k_arr                                 { $1 }
k_arr     : k_a DARROW k_arr                      { KArr($1, $3) }
          | k_a                                   { $1 }
k_a       : STAR                                  { KStar }
          | LPAREN k RPAREN                       { $2 }
k_o       :                                       { KStar }
          | COLONCOLON k                          { $2 }
t         : t_arr                                 { $1 }
          | ALL TX k_o DOT t                      { TAll($2,$3,$5) }
          | LAMBDA TX k_o DOT t                   { TAbs($2, $3, $5) }
t_arr     : t_app ARROW t_arr                     { TArr($1, $3) }
          | t_app                                 { $1 }
t_app     : t_app t_a                             { TApp($1, $2) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
          | UUNIT                                 { TUnit }
          | NAT                                   { TNat }
          | BOOL                                  { TBool }
m         : m_app                                 { $1 }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
          | LET X EQ m IN m                       { MLet($2, $4, $6) }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LETREC X COLON t EQ m IN m            { MLet($2, MFix(MAbs($2, $4, $6)), $8) }
          | LAMBDA TX k_o DOT m                   { MTAbs($2,$3,$5) }
m_app     : m_as                                  { $1 }
          | m_app m_a                             { MApp($1, $2) }
          | SUCC m_a                              { MSucc($2) }
          | PRED m_a                              { MPred($2) }
          | ISZERO m_a                            { MIsZero($2) }
          | FIX m_a                               { MFix($2) }
          | m_app LSQUARE t RSQUARE               { MTApp($1,$3) }
m_as      : m_a AS t                              { MAscribe($1, $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
          | UNIT                                  { MUnit }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | INTV                                  { m_of_int $1 }
b_t       :                                       { BTVar(KStar) }
          | COLONCOLON k                          { BTVar($2) }
          | t_args EQ t                           { BTAbb(addbinders $3 $1, None) }
b         : COLON t                               { BVar($2) }
          | EQ m                                  { BMAbb($2, None) }
t_args    :                                       { [] }
          | TX k_o t_args                         { ($1,$2)::$3 }
