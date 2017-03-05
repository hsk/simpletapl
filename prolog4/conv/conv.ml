open Syntax

(*
let rec f = function
  | Atom(x)           -> Atom(x)
  | Number(n)         -> Number(n)
  | Str(x)            -> Str(x)
  | Pred(x, xs)       -> Pred(x, fs xs)
  | Pre(x, xs)        -> Pre(x, f xs)
  | Post(xs,x)        -> Post(f xs, x)
  | Bin(t1, x, t2)    -> Bin(f t1, x, f t2)
  | Var(x)            -> Var(x)
  | Nil               -> Nil
  | Cons(x,y)         -> Cons(f x, f y)
and fs xs =
    List.map f xs
*)

let rec f = function
  | Pred("arr", [x;y]) -> Bin(f x, "->", f y)
  | Pred("record", [x]) -> Pred("{}",[f x])
  | Pred("fn", [x;t;e]) -> Bin(Pred("fn",[Bin(f x,":",f t)]),"->",f e)
  | Pred("tfn", [x;e]) -> Bin(Pred("fn",[f x]),"=>",f e)
  | Pred("tfn", [x;t;e]) -> Bin(Pred("fn",[Bin(f x,"::",f t)]),"=>",f e)
  | Pred("app", [x;y]) -> Bin(f x,"$",f y)
  | Pred("tapp", [x;y]) -> Bin(f x,"!",Pred("[]",[f y]))
  | Pred("typeof", [g;m;r]) -> Bin(f g,"/-",Bin(f m,":",f r))
  | Pred("teq", [g;m;r]) -> Bin(f g,"/-",Bin(f m,"=",f r))
  | Pred("teq2", [g;m;r]) -> Bin(f g,"/-",Bin(f m,"==",f r))

  | Pred("kindof", [g;m;r]) -> Bin(f g,"\\-",Bin(f m,"::",f r))
  | Pred("kindof1", [g;m;r]) -> Bin(f g,"/-",Bin(f m,"::",f r))
  | Pred("subtype", [g;m;r]) -> Bin(Bin(f g,"\\-",f m),"<:",f r)
  | Pred("subtype2", [g;m;r]) -> Bin(Bin(f g,"/-",f m),"<:",f r)
  | Pred("eval1", [g;m;r]) -> Bin(Bin(f g,"/-",f m),"==>",f r)
  | Pred("eval", [g;m;r]) -> Bin(Bin(f g,"/-",f m),"==>>",f r)
  | Bin(Pred("subtype", xs),":-",b) -> Bin(f (Pred("subtype", xs)),"where",f b)
  | Bin(Pred("subtype2", xs),":-",b) -> Bin(f (Pred("subtype2", xs)),"where",f b)
  | Bin(Pred("kindof", xs),":-",b) -> Bin(f (Pred("kindof", xs)),"where",f b)
  | Bin(Pred("kindof1", xs),":-",b) -> Bin(f (Pred("kindof1", xs)),"where",f b)
  | Bin(Pred("typeof", xs),":-",b) -> Bin(f (Pred("typeof", xs)),"where",f b)
  | Bin(Pred("eval1", xs),":-",b) -> Bin(f (Pred("eval1", xs)),"where",f b)
  | Bin(Pred("eval", xs),":-",b) -> Bin(f (Pred("eval", xs)),"where",f b)
  | Pred("eval1", [g;s;m;r;s2]) -> Bin(Bin(Bin(f g,"/",f s),"/-",f m),"==>",Bin(f r,"/",f s2))
  | Pred("eval", [g;s;m;r;s2]) -> Bin(Bin(Bin(f g,"/",f s),"/-",f m),"==>>",Bin(f r,"/",f s2))
  
  | Atom(x)           -> Atom(x)
  | Number(n)         -> Number(n)
  | Str(x)            -> Str(x)
  | Pred(x, xs)       -> Pred(x, fs xs)
  | Pre(x, xs)        -> Pre(x, f xs)
  | Post(xs,x)        -> Post(f xs, x)
  | Bin(t1, x, t2)    -> Bin(f t1, x, f t2)
  | Var(x)            -> Var(x)
  | Nil               -> Nil
  | Cons(x,y)         -> Cons(f x, f y)
and fs xs =
    List.map f xs

(*
:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,:: ]).
:- op(910, xfx, [ ⊢, /- ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1050,xfy, [->,=>]).
:- op(1200, xfx, [ --,iff,where ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).
term_expansion(A iff B, A :- B).
term_expansion(A where B, A :- B).

*)

let f m =
    opadd(500,Yfx,["$";"!"]);
    opadd(600,	Xfy,	["::"]);
    opadd(910, Xfx, ["/-";"\\-"]);
    opadd(920, Xfx, [ "==>"; "==>>";"<:" ]);
    opadd(1050, Xfy, [ "=>" ]);
    opadd(1200, Xfx, [ "--";"where" ]);
    let m = f m in
    let m = Bin(Post(Pred("term_expansion",[Bin(Var("A"),"where",Var("B"));Bin(Var("A"),":-",Var("B"))] ),"."),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("500");Atom("yfx");Pred("[]",[Atom("$");Atom("!")])] ),".")),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("600");Atom("xfy");Pred("[]",[Atom("::")])] ),".")),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("910");Atom("xfx");Pred("[]",[Atom("/-");Atom("\\-")])] ),".")),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("920");Atom("xfx");Pred("[]",[Atom("==>");Atom("==>>");Atom("<:")])] ),".")),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("1050");Atom("xfy");Pred("[]",[Atom("=>");])] ),".")),"@",m) in
    let m = Bin(Pre(":-",Post(Pred("op",[Number("1200");Atom("xfx");Pred("[]",[Atom("--");Atom("where")])] ),".")),"@",m) in
    m
