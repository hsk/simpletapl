%{
open Syntax
%}
%token <string> ATOM
%token <string> NUMBER
%token <string> STR
%token <string> VAR
%token <string> OP
%token <string> COMMENT
%token LPAREN RPAREN LBRACKET RBRACKET
%token COMMA BAR DOT
%token EOF

%start top
%type <Syntax.t> top
%%

s : { "" }
  | COMMENT s { $1 ^ $2 }

top : { Nil("") }
    | exp s DOT s top { Cons(Post($1,($2,".")),$4,$5) }

exp: { Nil("") }
    | exp1 s exp { Cons($1,$2,$3) }
    | exp1 s COMMA exp                    { Cons($1,"",Cons(Atom($2,","),"",$4)) }

exp1:        | s ATOM LPAREN exps RPAREN    { Pred(($1,$2), $4) }
             | s ATOM                       { Atom($1,$2) }
             | s VAR                        { Var($1,$2) }
             | s NUMBER                     { Number($1,$2) }
             | s STR                        { Str($1,$2) }
             | s LBRACKET exps RBRACKET     { Pred(($1,"[]"),$3) }
             | s LBRACKET RBRACKET          { Atom($1,"[]") }
             | s LPAREN exp RPAREN          { $3 }
             | s OP                         { Atom($1,$2) }
             | s BAR                      { Atom($1,"|") }

exp2: { Nil(xe) }
    | exp1 s exp2 { Cons($1,$2,$3) }

exps         : { [] }
             | exp2 { [$1] }
             | exp2 COMMA exps { $1::$3 }
             | exp2 s BAR exp { [Cons($1,$2,Cons(Atom($2,"|"),"",$4))] }
