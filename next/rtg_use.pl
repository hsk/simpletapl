:- use_module(rtg).

list(A)   ::= [] | [A|list(A)].
option(A) ::= none | some(A).
x ::= atom.

m ::=
      true
    | false
    | if(m,m,m)
    | 0
    | succ(m)
    | pred(m)
    | iszero(m)
    | x->m
    | fn(x)->m
    | op(option(m))
    | record(list(x))
    | record2(list(m))
    | record3(list(x:m))
    | record4(list(x=m))
    | {list(x=m)}
    .

:- m(true).
:- m(false).
:- m(if(true,true,true)).
:- m(0).
:- m(succ(0)).
:- m(pred(0)).
:- m(iszero(pred(0))).
:- m(x->true).
:- m(fn(x)->true).
:- m(op(some(true))).
:- m(record([a,b,c])).
:- m(record2([true,false])).
:- m(record3([a:true,b:false])).
:- m(record4([a=true,b=false])).
:- m({[a=true,b=false]}).
:- m(record3([a:true,b=false])). % error

:- halt.
