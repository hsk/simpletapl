%{
open Syntax
%}
%token <string> ATOM
%token <string> NUMBER
%token <string> STR
%token <string> VAR
%token <string> OP
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COMMA BAR DOT
%token EOF
%token <string> COMMENT
%start top
%type <Syntax.t> top
%%

s: { xe }
 | COMMENT s { $1 ^ $2 }
top: { Nil }
    | exp DOT s top { Cons(Post($1,(xe,".",$3)),$4) }

exp: { Nil }
    | exp1 exp { Cons($1,$2) }
    | exp1 COMMA exp                     { Cons($1,Cons(Atom(e","),$3)) }

exp1:        | s ATOM s LPAREN exps RPAREN s   { Pred(($1,$2,$3), $5,$7) }
             | s ATOM s                      { Atom($1,$2,$3) }
             | s VAR s                       { Var($1,$2,$3) }
             | s NUMBER s                   { Number($1,$2,$3) }
             | s STR s                       { Str($1,$2,$3) }
             | s LBRACKET s exps RBRACKET s    { Pred(($1,"[]",$3),$4,$6) }
             | s LBRACKET s RBRACKET          { Atom($1,"[]",$3) }
             | s LPAREN exp RPAREN          { $3 }
             | s LBRACE s exp RBRACE s         { Pred(($1,"{}",$3),[$4],$6) }
             | s OP s                        { Atom($1,$2,$3) }
             | s BAR s                     { Atom($1,"|",$3) }

exp2: { Nil }
    | exp1 exp2 { Cons($1,$2) }

exps         : { [] }
             | exp2 { [$1] }
             | exp2 COMMA exps { $1::$3 }
             | exp2 BAR s exp { [Cons($1,Cons(Atom(xe,"|",$3),$4))] }
