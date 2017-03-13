%test
a :- (a+b)+c,(c;b= ?).
a :- a+(b+c).
a :- (a*b)+(b*c)+a*b+b*c.
:- a.
:- b.
:- a,b.


m ::= %aaa
      true %g
    | pred(m) %b
    | iszero(m) %a
.
