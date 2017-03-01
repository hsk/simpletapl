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

let rec tmsubst j s = function
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

let rec maketop k =
  match k with
  | KStar -> TTop
  | KArr(k1,k2) -> TAbs("_",k1,maketop k2)

% ------------------------   EVALUATION  ------------------------

v(mAbs(_,_,_)).
v(mTAbs(_,_,_)).

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MTApp(MTAbs(x,_,m11),t2) -> tmsubst x t2 m11
  | MTApp(m1,t2) -> MTApp(eval1 g m1, t2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

% ------------------------   KINDING  ------------------------

let rec compute g = function
  | TApp(TAbs(x,_,t12),t2) -> tsubst x t2 t12
  | _ -> raise NoRuleApplies

let rec simplify g t =
  let t = 
    match t with
    | TApp(t1,t2) -> TApp(simplify g t1,t2)
    | t -> t
  in 
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq g s t =
  match (simplify g s, simplify g t) with
  | (TTop,TTop) -> true
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2
  | (TAbs(tx1,k1,s2),TAbs(_,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
  | (TApp(s1,s2),TApp(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | _ -> false

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
% (lambda X. lambda x:X. x) [All X.X->X]; 
% lambda x:Top. x;
% (lambda x:Top. x) (lambda x:Top. x);
% (lambda x:Top->Top. x) (lambda x:Top. x);
% lambda X<:Top->Top. lambda x:X. x x; 
