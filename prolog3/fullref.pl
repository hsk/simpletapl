:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | true | false | zero.
syntax(x). x(X) :- \+w(X),atom(X).
syntax(floatl). floatl(F) :- float(F).
syntax(stringl). stringl(F) :- string(F).
syntax(integer).
syntax(l). l(L) :- atom(L) ; integer(L).
list(A) ::= [] | [A|list(A)].

t ::= bool
    | nat
    | unit
    | float
    | string
    | top
    | bot
    | x
    | arr(t,t)
    | record(list(l:t))
    | variant(list(l:t))
    | ref(t)
    | source(t)
    | sink(t)
    .
m ::= true
    | false
    | if(m,m,m)
    | zero
    | succ(m)
    | pred(m)
    | iszero(m)
    | unit
    | floatl
    | timesfloat(m,m)
    | stringl
    | x
    | fn(x,t,m)
    | app(m,m)
    | let(x,m,m)
    | fix(m)
    | inert(t)
    | as(m,t)
    | record(list(l=m))
    | proj(m,l)
    | case(m,list(x=(x,m)))
    | tag(x,m,t)
    | loc(integer)
    | ref(m)
    | deref(m)
    | assign(m,m)
    .
n ::= zero
    | succ(n)
    .
v ::= true
    | false
    | n
    | unit
    | floatl
    | stringl
    | fn(x,t,m)
    | record(list(l=v))
    | tag(x,v,t)
    | loc(integer)
    .

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,top,top).
tsubst(J,S,bot,bot).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,variant(Mf),variant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,ref(T1),ref(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,source(T1),source(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,sink(T1),sink(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,unit,unit).
subst(J,M,F1,F1) :- float(F1).
subst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,X,X) :- string(X).
subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,fix(M1), fix(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,inert(T1), inert(T1)).
subst(J,M,as(M1,T1), as(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,tag(L,M1,T1), tag(L,M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,case(M1,Cases), case(M1_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst(J,M,ref(M1), ref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,deref(M1), deref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,assign(M1,M2), assign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,loc(L), loc(L)).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,some(T))).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

extendstore(St,V1,Len,St_) :- length(St,Len),append(St,[V1],St_).
lookuploc(St,L,R) :- nth0(L,St,R).
updatestore([_|St],0,V1,[V1|St]).
updatestore([V|St],N1,V1,[V|St_]) :- N is N1 - 1, updatestore(St,N,V1,St_).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

eval1(Γ,St,if(true,M2,M3),M2,St).
eval1(Γ,St,if(false,M2,M3),M3,St).
eval1(Γ,St,if(M1,M2,M3),if(M1_,M2,M3),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,succ(M1),succ(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,pred(zero),zero,St).
eval1(Γ,St,pred(succ(NV1)),NV1,St) :- n(NV1).
eval1(Γ,St,pred(M1),pred(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,iszero(zero),true,St).
eval1(Γ,St,iszero(succ(NV1)),false,St) :- n(NV1).
eval1(Γ,St,iszero(M1),iszero(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,timesfloat(F1,F2),F3,St) :- float(F1),float(F2),F3 is F1 * F2.
eval1(Γ,St,timesfloat(F1,M2),timesfloat(F1,M2_),St_) :- float(F1), eval1(Γ,St,M2,M2_).
eval1(Γ,St,timesfloat(M1,M2),timesfloat(M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,X,M,St) :- x(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,St,app(V1,M2),app(V1, M2_),St_) :- v(V1), eval1(Γ,St,M2,M2_,St_).
eval1(Γ,St,app(M1,M2),app(M1_, M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,St,let(X,M1,M2),let(X,M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(Γ,St,fix(M1),fix(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,as(V1,_), V1,St) :- v(V1).
eval1(Γ,St,as(M1,T), as(M1_,T),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,record(Mf),record(Mf_),St_) :- e(Mf,M,Mf_,M_),eval1(Γ,St,M,M_,St_).
eval1(Γ,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(Γ,St,proj(M1,L),proj(M1_, L),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,tag(L,M1,T),tag(L,M1_,T),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,case(tag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(Γ,St,case(M1,Bs),case(M1_, Bs),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(Γ,St,ref(M1),ref(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(Γ,St,deref(M1),deref(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(Γ,St,assign(V1,M2),assign(V1, M2_),St_) :- v(V1), eval1(Γ,St,M2,M2_,St_).
eval1(Γ,St,assign(M1,M2),assign(M1_, M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval(Γ,St,M,M_,St_) :- eval1(Γ,St,M,M1,St1),eval(Γ,St1,M1,M_,St_).
eval(Γ,St,M,M,St).

evalbinding(Γ,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(Γ,St,M,M_,St_).
evalbinding(Γ,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,X,T) :- x(X),gettabb(Γ,X,T).

simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,bool,bool).
teq2(Γ,nat,nat).
teq2(Γ,unit,unit).
teq2(Γ,float,float).
teq2(Γ,string,string).
teq2(Γ,top,top).
teq2(Γ,bot,bot).
teq2(Γ,X,T) :- x(X),gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,X) :- x(X),gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,X,X) :- x(X).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Γ,S,T)), Tf).
teq2(Γ,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Γ,S,T),Sf,Tf).
teq2(ref(S),ref(T)) :- teq(Γ,S,T).
teq2(source(S),source(T)) :- teq(Γ,S,T).
teq2(sink(S),sink(T)) :- teq(Γ,S,T).

subtype(Γ,S,T) :- teq(Γ,S,T).
subtype(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_), subtype2(Γ,S_,T_).
subtype2(Γ,_,top).
subtype2(Γ,bot,_).
subtype2(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype2(Γ,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(Γ,S,T)),TF).
subtype2(Γ,variant(SF),variant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(Γ,S,T)),SF).
subtype2(Γ,ref(S),ref(T)) :- subtype(Γ,S,T),subtype(Γ,T,S).
subtype2(Γ,ref(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,source(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,ref(S),sink(T)) :- subtype(Γ,T,S).
subtype2(Γ,sink(S),sink(T)) :- subtype(Γ,T,S).

join(Γ,S,T,T) :- subtype(Γ,S,T).
join(Γ,S,T,S) :- subtype(Γ,T,S).
join(Γ,S,T,R) :- simplify(Γ,S,S_),simplify(Γ,T,T_),join2(Γ,S_,T_,R).
join2(Γ,record(SF),record(TF),record(UF_)) :-
    include([L:_]>>member(L:_,TF),SF,UF),
    maplist([L:S,L:T_]>>(member(L:T,TF),join(Γ,S,T,T_)),UF,UF_).
join2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(Γ,S1,T1,S_),join(Γ,S2,T2,T_).
join2(Γ,ref(S),ref(T),ref(S)) :- subtype(Γ,S,T),subtype(Γ,T,S).
join2(Γ,ref(S),ref(T),source(T_)) :- /* Warning: this is incomplete... */ join(Γ,S,T,T_).

join2(Γ,source(S),source(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,ref(S),source(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,source(S),ref(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,sink(S),sink(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,ref(S),sink(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,sink(S),ref(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,_,_,top).

meet(Γ,S,T,S) :- subtype(Γ,S,T).
meet(Γ,S,T,T) :- subtype(Γ,T,S).
meet(Γ,S,T,R) :- simplify(Γ,S,S_),simplify(Γ,T,T_),meet2(Γ,S_,T_,R).
meet2(Γ,record(SF),record(TF),record(UF_)) :-
    maplist([L:S,L:T_]>>(member(L:T,TF),meet(Γ,S,T,T_);T_=S),SF,SF_),
    include([L:_]>>(\+member(L:_,SF)),TF,TF_),
    append(SF_,TF_,UF_).
meet2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(Γ,S1,T1,S_),meet(Γ,S2,T2,T_).
meet2(Γ,ref(S),ref(T),ref(T)) :- subtype(Γ,S,T), subtype(Γ,T,S).
meet2(Γ,ref(S),ref(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,source(S),source(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,ref(S),source(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,source(S),ref(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,sink(S),sink(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(Γ,ref(S),sink(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(Γ,sink(S),ref(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(_,_,bot).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T) :- typeof(Γ,M1,T1),subtype(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3),join(Γ,T2,T3,T).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,unit,unit).
typeof(Γ,F1,float) :- float(F1).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),subtype(Γ,T1,float),typeof(Γ,M2,T2),subtype(Γ,T2,float).
typeof(Γ,X,string) :- string(X).
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),bot) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),simplify(Γ,T1,bot).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),subtype(Γ,T12,T11).
typeof(Γ,fix(M1),bot) :- typeof(Γ,M1,T1),simplify(Γ,T1,bot).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- typeof(Γ,M1,T1),subtype(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),simplify(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,proj(M1,L),bot) :- typeof(Γ,M1,T1),simplify(Γ,T1,bot).
typeof(Γ,tag(Li, Mi, T), T) :- simplify(Γ,T,variant(Tf)),member(Li:Te,Tf),typeof(Γ,Mi, T_),subtype(Γ,T_,Te).
typeof(Γ,case(M, Cases), bot) :- typeof(Γ,M,T),simplify(Γ,T,bot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases).
typeof(Γ,case(M, Cases), T_) :-
    typeof(Γ,M,T),simplify(Γ,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases,CaseTypes),
    foldl(join(Γ),bot,CaseTypes,T_).

typeof(Γ,ref(M1),ref(T1)) :- typeof(Γ,M1,T1).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), simplify(Γ,T,ref(T1)).
typeof(Γ,deref(M1),bot) :- typeof(Γ,M1,T), simplify(Γ,T,bot).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), simplify(Γ,T,source(T1)).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), simplify(Γ,T,ref(T1)),typeof(Γ,M2,T2),subtype(Γ,T2,T1).
typeof(Γ,assign(M1,M2),bot) :- typeof(Γ,M1,T), simplify(Γ,T,bot),typeof(Γ,M2,_).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), simplify(Γ,T,sink(T1)),typeof(Γ,M2,T2),subtyping(Γ,T2,T1).

typeof(Γ,loc(l),_) :- !,fail.
%typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.
% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar,'').
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(Γ,bTAbb(T),' :: *').

run(eval(M),(Γ,St),(Γ,St_)) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,St,M,M_,St_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),(Γ,St),([X-Bind|Γ],St_)) :-
  typeof(Γ,M,T),evalbinding(Γ,St,bMAbb(M,some(T)),Bind,St_),write(X),show_bind(Γ,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),(Γ,St),([X-Bind|Γ],St_)) :-
  typeof(Γ,M,T_),teq(Γ,T_,T),evalbinding(Γ,St,bMAbb(M,some(T)),Bind,St_),show_bind(Γ,Bind,S),write(X),writeln(S).
run(bind(X,Bind),(Γ,St),([X-Bind_|Γ],St_)) :-
  evalbinding(Γ,St,Bind,Bind_,St_),show_bind(Γ,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(fn(x,bot,x))]).
% lambda x:Bot. x x;
:- run([eval(fn(x,bot,app(x,x)))]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(fn(x,variant([a:bool,b:bool]),x))]).
% lambda x:Top. x;
:- run([eval(fn(x,top,x))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,x),fn(x,top,x)))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(r,arr(top,top),app(r,r)),
                  fn(z,top,z))) ]).
% (lambda r:{x:Top->Top}. r.x r.x)
%   {x=lambda z:Top.z, y=lambda z:Top.z};
:- run([eval(app(fn(r,record([x:arr(top,top)]),app(proj(r,x),proj(r,x))),
                  record([x=fn(z,top,z),y=fn(z,top,z)])))]).
% "hello";
:- run([eval("hello")]).
% unit;
:- run([eval(unit)]).
% lambda x:A. x;
:- run([eval(fn(x,'A',x))]).
% let x=true in x;
:- run([eval(let(x,true,x))]).
% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([eval(if(true,record([x=true,y=false,a=false]),record([y=false,x=record([]),b=false])))]).
% timesfloat 2.0 3.14159;
:- run([eval(timesfloat(2.0,3.14159))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,x))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(fn(x,nat, succ(x)))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(app(fn(x,nat, succ(succ(x))),succ(zero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(arr(nat,nat))),
        eval(fn(f,'T',fn(x,nat,app(f,app(f,x)))))]).
% let a = ref 1 in !a;
:- run([eval(let(a,ref(succ(zero)),deref(a)))]).
% let a = ref 2 in (a := (succ (!a)); !a);
:- run([eval(let(a,ref(succ(succ(zero))),let('_',assign(a,succ(deref(a))),deref(a)))) ]).

:- halt.
