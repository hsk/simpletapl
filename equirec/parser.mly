%{
open Syntax
%}
%token LAMBDA
%token REC
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
b         : COLON t                               { BVar($2) }
t         : t_arr                                 { $1 }
          | REC TX DOT t                          { TRec($2,$4) }
t_arr     : t_a ARROW t_arr                       { TArr($1, $3) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
m         : m_app                                 { $1 }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
m_app     : m_a                                   { $1 }
          | m_app m_a                             { MApp($1, $2) }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
