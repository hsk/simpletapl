%{
open Syntax
%}
%token TRUE FALSE IF THEN ELSE BOOL
%token LAMBDA
%token TTOP
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
b         : COLON t                               { BVar($2) }
t         : t_a ARROW t                           { TArr($1, $3) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TTOP                                  { TTop }
          | LCURLY t_fls RCURLY                   { TRecord($2) }
          | BOOL                                  { TBool }
t_fls     :                                       { [] }
          | t_fls_ne                              { $1 1 }
t_fls_ne  : t_fl                                  { fun i -> [$1 i] }
          | t_fl COMMA t_fls_ne                   { fun i -> ($1 i)::($3 (i+1)) }
t_fl      : X COLON t                             { fun i -> ($1, $3) }
          | t                                     { fun i -> (string_of_int i, $1) }
m         : m_app                                 { $1 }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
m_app     : m_path                                { $1 }
          | m_app m_path                          { MApp($1, $2) }
m_path    : m_path DOT X                          { MProj($1, $3) }
          | m_path DOT INTV                       { MProj($1, string_of_int $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m RPAREN                       { $2 }
          | X                                     { MVar($1) }
          | LCURLY fls RCURLY                     { MRecord($2 1) }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
fls       :                                       { fun i -> [] }
          | fls_ne                                { $1 }
fls_ne    : fl                                    { fun i -> [$1 i] }
          | fl COMMA fls_ne                       { fun i -> ($1 i) :: ($3 (i+1)) }
fl        : X EQ m                                { fun i -> ($1, $3) }
          | m                                     { fun i -> (string_of_int i, $1) }
