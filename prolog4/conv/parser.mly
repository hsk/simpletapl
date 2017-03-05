%{
open Syntax
%}
%token <string> ATOM
%token <string> NUMBER
%token <string> STR
%token <string> VAR
%token <string> OP
%token LPAREN RPAREN LBRACKET RBRACKET
%token COMMA BAR
%token EOF

%start exp
%type <Syntax.t> exp
%%

exp: { Nil }
    | exp1 exp { Cons($1,$2) }
    | COMMA exp                     { Cons(Atom ",",$2) }

exp1:        | ATOM LPAREN exps RPAREN    { Pred($1, $3) }
             | ATOM                       { Atom $1 }
             | VAR                        { Var($1) }
             | NUMBER                     { Number $1 }
             | STR                        { Str $1 }
             | LBRACKET exps RBRACKET     { Pred("[]",$2) }
             | LBRACKET RBRACKET          { Atom("[]") }
             | LPAREN exp RPAREN          { $2 }
             | OP                         { Atom $1 }
             | BAR                      { Atom "|" }

exp2: { Nil }
    | exp1 exp2 { Cons($1,$2) }

exps         : { [] }
             | exp2 { [$1] }
             | exp2 COMMA exps { $1::$3 }
             | exp2 BAR exp { [Cons($1,Cons(Atom"|",$3))] }
