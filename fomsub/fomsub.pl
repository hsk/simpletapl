% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,tTop,tTop).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_), tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tAbs(TX,K,T2),tAbs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tApp(T1,T2),tApp(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,mVar(J),M).
subst(J,M,mVar(X),mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,mTAbs(TX,T1,M2),mTAbs(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,mTApp(M1,T2),mTApp(M1_,T2)) :- subst(J,M,M1,M1_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mTAbs(TX,T1,M2),mTAbs(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,mTApp(M1,T2),mTApp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

maketop(kStar, tTop).
maketop(kArr(K1,K2),tAbs('_',K1,K2_)) :- maketop(K2,K2_).

% ------------------------   EVALUATION  ------------------------

v(mAbs(_,_,_)).
v(mTAbs(_,_,_)).

eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mApp(V1,M2),mApp(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mTApp(mTAbs(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,mTApp(M1,T2),mTApp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   KINDING  ------------------------

compute(G,tApp(tAbs(X,_,T12),T2),T) :- tsubst(X,T2,T12,T).
simplify(G,tApp(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,tApp(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tTop,tTop).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(tAll(TX,S1,S2),tAll(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).
teq2(tAbs(TX,K1,S2),tAbs(_,K1,T2)) :- teq([TX-bName|g],S2,T2).
teq2(G,tApp(S1,S2),tApp(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

let rec kindof g = function
  | TVar(x) when not (List.mem_assoc x g) -> KStar
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> kindof g t
      | _ -> failwith ("getkind: Wrong kind of binding for variable " ^ x)
      end
  | TArr(t1,t2) -> checkkindstar g t1; checkkindstar g t2; KStar
  | TAll(tx,t1,t2) -> checkkindstar ((tx,BTVar t1)::g) t2; KStar
  | TAbs(tx,k1,t2) -> KArr(k1, kindof ((tx,BTVar(maketop k1))::g) t2)
  | TApp(t1,t2) ->
      let k1 = kindof g t1 in
      let k2 = kindof g t2 in
      begin match k1 with
      | KArr(k11,k12) ->
          if k2 = k11 then k12 else failwith "parameter kind mismatch"
      | _ -> failwith "arrow kind expected"
      end
  | _ -> KStar

and checkkindstar g t = 
  if kindof g t <> KStar then failwith "Kind * expected"

% ------------------------   SUBTYPING  ------------------------

let rec promote g = function
  | TVar(x) ->
      begin try match getb g x with
      | BTVar(t) -> t
      | _ -> raise NoRuleApplies
      with _ -> raise NoRuleApplies
      end
  | TApp(s,t) -> TApp(promote g s,t)
  | _ -> raise NoRuleApplies

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
  | (TVar(_) as s,t) -> subtype g (promote g s) t
  | (TApp(_,_) as s,t) -> subtype g (promote g s) t
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
  | (TAbs(tx,k1,s2),TAbs(_,k2,t2)) -> k1 = k2 && subtype ((tx,BTVar(maketop k1))::g) s2 t2
  | (_,_) -> false

% ------------------------   TYPING  ------------------------

let rec lcst g s =
  let s = simplify g s in
  try lcst g (promote g s) with NoRuleApplies -> s

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> checkkindstar g t1; TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match lcst g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MTAbs(tx,t1,m2) -> TAll(tx,t1,typeof ((tx,BTVar(t1))::g) m2)
  | MTApp(m1,t2) ->
      begin match lcst g (typeof g m1) with
      | TAll(x,t11,t12) ->
          if not(subtype g t2 t11) then failwith "type parameter type mismatch";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' :: %w',[T]). 

let _ = 
  let filename = ref "" in
  Arg.parse [] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
  List.fold_left (fun g -> function
    | Eval(m)->
      let t = typeof g m in
      let m = eval g m in
      Printf.printf "%s : %s\n" (show m) (show_t t);
      g
    | Bind(x,bind) ->
      Printf.printf "%s%s\n" x (show_bind g bind);
      (x,bind)::g
  ) [] (parseFile !filename) 

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x; 
:- run([eval(mTAbs('X',mAbs(x,'X',mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% lambda X<:Top->Top. lambda x:X. x x; 
