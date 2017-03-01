% ------------------------   SUBSTITUTION  ------------------------

let rec subst j s = function
    | MVar(x) -> if x=j then s else MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
    | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
   match getb a x with
   | BVar(t) -> t
   | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 

% ------------------------   EVALUATION  ------------------------

let rec v = function
  | MAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

% ------------------------   SUBTYPING  ------------------------

let rec subtype s t =
   s = t ||
   match (s,t) with
   | (_,TTop) -> true
   | (TBot,_) -> true
   | (TArr(s1,s2),TArr(t1,t2)) -> subtype t1 s1 && subtype s2 t2
   | (_,_) -> false

% ------------------------   TYPING  ------------------------

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t2 = typeof g m2 in
      begin match typeof g m1 with
      | TArr(t11,t12) ->
          if subtype t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

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

% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tArr),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% lambda x:Bot. x;
:- run([eval(mAbs(x,tBot,mVar(x)))]).
% lambda x:Bot. x x;
:- run([eval(mAbs(x,tBot,mApp(mVar(x),mVar(x))))]).
% y:Bot->Bot;
% x:Bot;
% y x;
:- run([bind(y,bVar(tArr(tBot,tBot))),
        bind(x,bVar(tBot)),
        eval(mApp(mVar(y),mVar(x)))]).
