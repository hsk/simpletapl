%{
open Syntax
let rec m_of_int = function
    | 0 -> MZero
    | n -> MSucc(m_of_int (n-1))
%}
%token TRUE FALSE IF THEN ELSE
%token SUCC PRED ISZERO
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
m         : m_app                                 { $1 }
          | IF m THEN m ELSE m                    { MIf($2,$4,$6) }
m_app     : m_a                                   { $1 }
          | SUCC m_a                              { MSucc($2) }
          | PRED m_a                              { MPred($2) }
          | ISZERO m_a                            { MIsZero($2) }
m_a       : LPAREN m RPAREN                       { $2 }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | INTV                                  { m_of_int $1 }
