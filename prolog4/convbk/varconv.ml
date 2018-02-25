open Syntax

let vars = ref []

let rec find = function
  | Pred("var", [x])  -> vars := Pred("val",[x])::!vars; x
  | Atom(x)           -> Atom(x)
  | Number(n)         -> Number(n)
  | Str(x)            -> Str(x)
  | Pred(x, es)       -> Pred(x, finds es)
  | Pre(x, e)        -> Pre(x, find e)
  | Post(e,x)        -> Post(find e, x)
  | Bin(e1, x, e2)    -> Bin(find e1, x, find e2)
  | Var(x)            -> Var(x)
  | Nil               -> Nil
  | Cons(e1,e2)         -> Cons(find e1, find e1)
and finds es =
    List.map find es

let find e =
    let e = find e in
    let vs = !vars in
    vars := [];
    (e,vs)

let rec mkval (x::xs) =
    List.fold_left(fun x e ->Bin(x,",",e)) x xs

let rec f = function
  | Post(Pre(":-", xs),".") as e -> e
  | Post(a,".") ->
    begin match find a with
    | (e,[]) -> Post(e,".")
    | (e,xs) -> Bin(e,"where",Post(mkval (List.rev xs),"."))
    end
  | Bin(a,":-",Post(b,".")) ->
    begin match find a with
    | (e,[]) -> Bin(a,"where",Post(f b,"."))
    | (e,xs) -> Bin(e,"where",Post(mkval (List.rev(f b::xs)),"."))
    end
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

let f m =
    let m = f m in
    let m = Bin(Bin(Pred("val",[Var("X")]),":-",Post(Pred("atom",[Var("X")]),".")),"@",m) in
    m

let f m = m
