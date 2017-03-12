%test
a :- a,b,c,(b= ? ; c).
a :- a,b.
a :- a,b.
:- a.
:- b.
:- a,b.


m ::= %aaa
      true %g
    | false %f
    | if(m, m, m)  %e
    | 0  %d
    | succ(m) %c
    | pred(m) %b
    | iszero(m) %a
.
