% ------------------------   SUBSTITUTION  ------------------------

let rec subst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst2 x j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | MAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 g m1, m2, m3)
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | (* Insert case(s) for MLet here *) _ -> assert false
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

% ------------------------   TYPING  ------------------------

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
     if typeof g m1 = TBool then
       let t2 = typeof g m2 in
       if t2 = typeof g m3 then t2
       else failwith "arms of conditional have different types"
     else failwith "guard of conditional not g boolean"
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match t1 with
      | TArr(t11,t12) ->
          if t2 = t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | (* Insert case(s) for MLet here *) _ -> assert false

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
    | Bind(x,b) ->
      Printf.printf "%s%s\n" x (show_bind g b);
      (x,b)::g
  ) [] (parseFile !filename) 

% ------------------------   TEST  ------------------------

% lambda x:Bool. x;
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
