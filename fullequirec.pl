:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,tBool,tBool).
tsubst(J,S,tNat,tNat).
tsubst(J,S,tUnit,tUnit).
tsubst(J,S,tFloat,tFloat).
tsubst(J,S,tString,tString).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tRecord(Mf),tRecord(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,tVariant(Mf),tVariant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,tRec(X,T1),tRec(X,T1_)) :- tsubst2(X,J,S,T1,T1_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPred(M1),mPred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mUnit,mUnit).
subst(J,M,mFloat(F1),mFloat(F1)).
subst(J,M,mTimesfloat(M1,M2), mTimesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mString(X),mString(X)).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,mFix(M1), mFix(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mInert(T1), mInert(T1)).
subst(J,M,mAscribe(M1,T1), mAscribe(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,mProj(M1,L),mProj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,mTag(L,M1,T1), mTag(L,M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,mCase(M,Cases), mCase(M_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mUnit).
v(mFloat(_)).
v(mString(_)).
v(mAbs(_,_,_)).
v(mRecord(Mf)) :- maplist([L=M]>>v(M),Mf).
v(mTag(_,M1,_)) :- v(M1).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mIf(M1,M2,M3),mIf(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,mSucc(M1),mSucc(M1_)) :- eval1(G,M1,M1_).
eval1(G,mPred(mZero),mZero).
eval1(G,mPred(mSucc(N1)),N1) :- n(N1).
eval1(G,mPred(M1),mPred(M1_)) :- eval1(G,M1,M1_).
eval1(G,mIsZero(mZero),mTrue).
eval1(G,mIsZero(mSucc(N1)),mFalse) :- n(N1).
eval1(G,mIsZero(M1),mIsZero(M1_)) :- eval1(G,M1,M1_).
eval1(G,mTimesfloat(mFloat(F1),mFloat(F2)),mFloat(F3)) :- F3 is F1 * F2.
eval1(G,mTimesfloat(V1,M2),mTimesfloat(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mTimesfloat(M1,M2),mTimesfloat(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mLet(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,mLet(X,M1,M2),mLet(X,M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mFix(mAbs(X,T,M12)),M12_) :- subst(X,mFix(mAbs(X,T,M12)),M12,M12_).
eval1(G,mFix(M1),mFix(M1_)) :- eval1(G,M1,M1_).
eval1(G,mAscribe(V1,_), V1) :- v(V1).
eval1(G,mAscribe(M1,T), mAscribe(M1_,T)) :- eval1(G,M1,M1_).
eval1(G,mRecord(Mf),mRecord(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,mProj(mRecord(Mf),L),M) :- member(L=M,Mf).
eval1(G,mProj(M1,L),mProj(M1_, L)) :- eval1(G,M1,M1_).
eval1(G,mTag(L,M1,T),mTag(L,M1_,T)) :- eval1(G,M1,M1_).
eval1(G,mCase(mTag(L,V11,_),Bs),M_) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(G,mCase(M1,Bs),mCase(M1_, Bs)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).
  
gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,tRec(X,S1),T) :- tsubst(X,tRec(X,S1),S1,T).
compute(G,tVar(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- teq([],G,S,T).
teq(Seen,G,S,T) :- member((S,T),Seen).
teq(Seen,G,tBool,tBool).
teq(Seen,G,tNat,tNat).
teq(Seen,G,tUnit,tUnit).
teq(Seen,G,tFloat,tFloat).
teq(Seen,G,tString,tString).
teq(Seen,G,tRec(X,S1),T) :- S=tRec(X,S1),tsubst(X,S,S1,S1_),teq([(S,T)|Seen],G,S1_,T).
teq(Seen,G,S,tRec(X,T1)) :- T=tRec(X,T1),tsubst(X,T,T1,T1_),teq([(S,T)|Seen],G,S,T1_).
teq(Seen,G,tVar(X),tVar(X)).
teq(Seen,G,tVar(X),T) :- gettabb(G,X,S),teq(Seen,G,S,T).
teq(Seen,G,S,tVar(X)) :- gettabb(G,X,T),teq(Seen,G,S,T).
teq(Seen,G,tArr(S1,S2),tArr(T1,T2)) :- teq(Seen,G,S1,T1),teq(Seen,G,S2,T2).
teq(Seen,G,tRecord(Sf),tRecord(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Seen,G,S,T)), Tf).
teq(Seen,G,tVariant(Sf),tVariant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Seen,G,S,T),Sf,Tf).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mUnit,tUnit).
typeof(G,mFloat(_),tFloat).
typeof(G,mTimesfloat(M1,M2),tFloat) :- typeof(G,M1,T1),teq(G,T1,tFloat),typeof(G,M2,T2),teq(G,T2,tFloat).
typeof(G,mString(_),tString).
typeof(G,mVar(X),T) :- gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,mLet(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,mFix(M1),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),teq(G,T12,T11).
typeof(G,mInert(T),T).
typeof(G,mAscribe(M1,T),T) :- typeof(G,M1,T1),teq(G,T1,T).
typeof(G,mRecord(Mf),tRecord(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,mProj(M1,L),T) :- typeof(G,M1,T1),simplify(G,T1,tRecord(Tf)),member(L:T,Tf).
typeof(G,mTag(Li, Mi, T), T) :- simplify(G,T,tVariant(Tf)),member(Li:Te,Tf),typeof(G,Mi, T_),teq(G,T_,Te).
typeof(G,mCase(M, Cases), T1) :-
    typeof(G,M,T),simplify(G,T,tVariant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases,[T1|RestT]),
    maplist([Tt]>>teq(G,Tt,T1), RestT).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% "hello";
:- run([eval(mString(hello))]).
% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
% timesfloat 2.0 3.14159;
:- run([eval(mTimesfloat(mFloat(2.0),mFloat(3.14159))) ]).
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'),mAbs(x,tNat,mApp(mVar(f),mApp(mVar(f),mVar(x))))))]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([eval(mAbs(f,tRec('X',tArr(tVar('A'),tVar('A'))),mAbs(x,tVar('A'),mApp(mVar(f),mVar(x)))))]).
% {x=true, y=false};
:- run([eval(mRecord([x=mTrue,y=mFalse])) ]).
% {x=true, y=false}.x;
:- run([eval(mProj(mRecord([x=mTrue,y=mFalse]),x)) ]).
% {true, false};
:- run([eval(mRecord([1=mTrue,2=mFalse])) ]).
% {true, false}.1;
:- run([eval(mProj(mRecord([1=mTrue,2=mFalse]),1)) ]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(mAbs(x,tVariant([a:tBool,b:tBool]),mVar(x)))]).

% Counter = Rec P. {get:Nat, inc:Unit->P};
% p = 
%   let create = 
%     fix 
%       (lambda cr: {x:Nat}->Counter.
%         lambda s: {x:Nat}.
%           {get = s.x,
%           inc = lambda _:Unit. cr {x=succ(s.x)}})
%   in
%     create {x=0};
% p1 = p.inc unit;
% p1.get;
% get = lambda p:Counter. p.get;
% inc = lambda p:Counter. p.inc;
:- run([
  bind('Counter',bTAbb(tRec('P',tRecord([get:tNat,inc:tArr(tUnit,tVar('P'))])))),
  bind(p,bMAbb(mLet(create,
    mFix(
      mAbs(cr,tArr(tRecord([x:tNat]),tVar('Counter')),
        mAbs(s,tRecord([x:tNat]),
          mRecord([get=mProj(mVar(s),x),
            inc=mAbs('_',tUnit, mApp(mVar(cr),mRecord([x=mSucc(mProj(mVar(s),x))])))
          ])
        )
      )
    ),
    mApp(mVar(create),mRecord([x=mZero]))),none )),
  eval(mProj(mVar(p),get)),
  bind(p,bMAbb(mApp(mProj(mVar(p),inc),mUnit ),none )),
  eval(mProj(mVar(p),get)),
  bind(p,bMAbb(mApp(mProj(mVar(p),inc),mUnit ),none )),
  eval(mProj(mVar(p),get)),
  bind(get,bMAbb(mAbs(p,tVar('Counter'),mProj(mVar(p),get)),none)),
  bind(inc,bMAbb(mAbs(p,tVar('Counter'),mProj(mVar(p),inc)),none)),
  eval(mApp(mVar(get),mVar(p))),
  bind(p,bMAbb(mApp(mApp(mVar(inc),mVar(p)),mUnit),none)),
  eval(mApp(mVar(get),mVar(p)))
]).

% Hungry = Rec A. Nat -> A;
% f0 =
% fix 
%   (lambda f: Nat->Hungry.
%    lambda n:Nat.
%      f);
% f1 = f0 0;
% f2 = f1 2;

% T = Nat;
%   
% fix_T = 
% lambda f:T->T.
%   (lambda x:(Rec A.A->T). f (x x))
%   (lambda x:(Rec A.A->T). f (x x));

% D = Rec X. X->X;
% fix_D = 
% lambda f:D->D.
%   (lambda x:(Rec A.A->D). f (x x))
%   (lambda x:(Rec A.A->D). f (x x));
% diverge_D = lambda _:Unit. fix_D (lambda x:D. x);
% lam = lambda f:D->D. f;
% ap = lambda f:D. lambda a:D. f a;
% myfix = lam (lambda f:D.
%              ap (lam (lambda x:D. ap f (ap x x))) 
%                 (lam (lambda x:D. ap f (ap x x))));


% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% unit;
:- run([eval(mUnit)]).

% NatList = Rec X. <nil:Unit, cons:{Nat,X}>; 
% nil = <nil=unit> as NatList;
% cons = lambda n:Nat. lambda l:NatList. <cons={n,l}> as NatList;
% isnil = lambda l:NatList. 
% case l of
% <nil=u> ==> true
% | <cons=p> ==> false;
% hd = lambda l:NatList. 
%  case l of
%   <nil=u> ==> 0
%  | <cons=p> ==> p.1;
% tl = lambda l:NatList. 
%   case l of
%   <nil=u> ==> l
%   | <cons=p> ==> p.2;
% plus = fix (lambda p:Nat->Nat->Nat. 
%  lambda m:Nat. lambda n:Nat. 
%  if iszero m then n else succ (p (pred m) n));
% sumlist = fix (lambda s:NatList->Nat. lambda l:NatList.
%  if isnil l then 0 else plus (hd l) (s (tl l)));
% mylist = cons 2 (cons 3 (cons 5 nil));
% sumlist mylist;

:- halt.
