%{
open Syntax
%}
%token LAMBDA
%token TTOP LEQ
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
b_t       :                                       { BTVar(TTop) }
          | LEQ t                                 { BTVar($2) }
b         : COLON t                               { BVar($2) }
t         : t_arr                                 { $1 }
          | ALL TX t_o DOT t                      { TAll($2, $3, $5) }
t_o       :                                       { TTop }
          | LEQ t                                 { $2 }
t_arr     : t_a ARROW t_arr                       { TArr($1, $3) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
          | TTOP                                  { TTop }
m         : m_app                                 { $1 }
          | LAMBDA TX t_o DOT m                   { MTAbs($2,$3,$5) }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
m_app     : m_a                                   { $1 }
          | m_app LSQUARE t RSQUARE               { MTApp($1, $3) }
          | m_app m_a                             { MApp($1, $2) }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
