%{
open Syntax
%}
%token LAMBDA
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
m         : m_app                                 { $1 }
          | LAMBDA X DOT m                        { MAbs($2, $4) }
m_app     : m_a                                   { $1 }
          | m_app m_a                             { MApp($1, $2) }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
