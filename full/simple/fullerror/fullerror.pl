% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mTry(M1,M2), mTry(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mError, mError).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(mTrue).
v(mFalse).
v(mAbs(_,_,_)).

let nv m1 = not(v m1)

let rec eval_context = function
  | MIf(m1,m2,m3) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MIf(f m1, m2,m3))
  | MApp(m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MApp(f m1, m2))
  | MApp(v1,m2) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MApp(v1, f m2))
  | MTry(m1,m2) when nv m1 -> (MTry(m1,m2), fun m1->m1)
  | m1 when nv m1 -> (m1, fun m1 -> m1)
  | _ ->  raise NoRuleApplies

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m 
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MTry(MError, m2) -> m2
  | MTry(v1, m2) when v v1 -> v1
  | MTry(m1, m2) -> MTry(eval1 g m1,m2)
  | MError -> raise NoRuleApplies
  | m ->
      match eval_context m with
      | MError,f -> MError
      | h,f when h=m -> raise NoRuleApplies
      | h,f -> f (eval1 g h)

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let evalbinding g = function
  | BMAbb(m,t) -> BMAbb(eval g m,t)
  | bind -> bind

% ------------------------   SUBTYPING  ------------------------

let istabb g x = 
  try match getb g x with
  | BTAbb(t) -> true
  | _ -> false
  with _ -> false

let gettabb g x = 
  match getb g x with
  | BTAbb(t) -> t
  | _ -> raise NoRuleApplies

let rec compute g = function
  | TVar(x) when istabb g x -> gettabb g x
  | _ -> raise NoRuleApplies

let rec simplify g t =
  try simplify g (compute g t)
  with NoRuleApplies -> t

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tBool,tBool).
teq2(G,tTop,tTop).
teq2(G,tBot,tBot).
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

let rec subtype g s t =
   teq g s t ||
   match (simplify g s, simplify g t) with
   | (_,TTop) -> true
   | (TBot,_) -> true
   | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
   | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(meet g s1 t1, join g s2 t2)
  | _ -> TTop

and meet g s t =
  if subtype g s t then s else 
  if subtype g t s then t else 
  match (simplify g s, simplify g t) with
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | _ -> TBot

% ------------------------   TYPING  ------------------------

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
      if subtype g (typeof g m1) TBool then
        join g (typeof g m2) (typeof g m3)
      else failwith "guard of conditional not g boolean"
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MTry(m1,m2) -> join g (typeof g m1) (typeof g m2)
  | MError -> TBot

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

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
      let bind =
        match bind with
        | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
        | BMAbb(m,Some(t)) ->
          let t' = typeof g m in
          if teq g t' t then BMAbb(m,Some(t))
          else failwith "Type of b does not match declared type"
        | bind -> bind
      in
      let bind = evalbinding g bind in
      Printf.printf "%s%s\n" x (show_bind g bind);
      (x,bind)::g
  ) [] (parseFile !filename) 

/* Examples for testing */

% lambda x:Bot. x;
% lambda x:Bot. x x; 

% lambda x:Top. x;
%  (lambda x:Top. x) (lambda x:Top. x);
% (lambda x:Top->Top. x) (lambda x:Top. x);


% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]). 
% if error then true else false;


% error true;
% (lambda x:Bool. x) error;

% T = Bool;
% a = true;
% a;

% try error with true;
% try if true then error else true with false;
