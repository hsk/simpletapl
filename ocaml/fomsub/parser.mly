%{
open Syntax
%}
%token LAMBDA
%token TTOP
%token LEQ
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
          | COLONCOLON k                          { BTVar(maketop ($2)) }
b         : COLON t                               { BVar($2) }
k_o       :                                       { KStar }
          | COLONCOLON k                          { $2 }
k         : k_arr                                 { $1 }
k_arr     : k_a DARROW k_arr                      { KArr($1, $3) }
          | k_a                                   { $1 }
k_a       : STAR                                  { KStar }
          | LPAREN k RPAREN                       { $2 }
t_o       :                                       { TTop }
          | LEQ t                                 { $2 }
          | COLONCOLON k                          { maketop ($2) }
t         : t_arr                                 { $1 }
          | ALL TX t_o DOT t                      { TAll($2, $3, $5) }
          | LAMBDA TX k_o DOT t                   { TAbs($2, $3, $5) }
t_arr     : t_app ARROW t_arr                     { TArr($1, $3) }
          | t_app                                 { $1 }
t_app     : t_app t_a                             { TApp($1, $2) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TTOP                                  { TTop }
          | TX                                    { TVar($1) }
          | TTOP LSQUARE k RSQUARE                { maketop ($3) }
m         : m_app                                 { $1 }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
          | LAMBDA TX t_o DOT m                   { MTAbs($2,$3,$5) }
m_app     : m_a                                   { $1 }
          | m_app m_a                             { MApp($1, $2) }
          | m_app LSQUARE t RSQUARE               { MTApp($1, $3) }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
