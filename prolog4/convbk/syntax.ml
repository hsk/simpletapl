type x = string * string
let xe = ""
type t =
  | Atom of x
  | Number of x
  | Str of x
  | Pred of x * t list
  | Post of t * x
  | Pre of x * t
  | Bin of t * x * t
  | Var of x
  | Cons of t * string * t
  | Nil of string

let e t = (xe,t)

type opp = Xfx|Yfx|Fx|Fy|Xfy|Xf|Yf

let show_o = function
  |Xfx -> "xfx"
  |Yfx -> "xyx"
  |Fx -> "fx"
  |Fy -> "fy"
  |Xfy -> "xfy"
  |Xf -> "xf"
  |Yf -> "yf"


let ops = [
    1300,	Xf,	["."]; (* added *)
    1200,	Xfx,	["-->"; ":-"; "::="(*added*)];
    1190,	Fx,	[":-"; "?-"];
    1150,	Fx,	["dynamic"; "discontiguous"; "initialization"; "meta_predicate";"module_transparent"; "multifile"; "public"; "thread_local";"thread_initialization"; "volatile"];
    1100,	Xfy,	[";"];
    (*1100,	Xfy,	[";"; "|"];*)
    1050,	Xfy,	["->"; "*->"];
    1000,	Xfy,	[","];

    995,  Xfy,  ["|"];(* change *)

    990,	Xfx,	[":="];
    900,	Fy,	["\\+"];
    700,	Xfx,	["<"; "="; "=.."; "=@="; "\\=@="; "=:="; "=<"; "=="; "=\\="; ">"; ">="; "@<"; "@=<"; "@>"; "@>="; "\\="; "\\=="; "as"; "is"; ">:<"; ":<"];
    600,	Xfy,	[":"];
    500,	Yfx,	["+"; "-"; "/\\"; "\\/"; "xor"];
    500,	Fx,	["?"];
    400,	Yfx,	["*"; "/"; "//"; "div"; "rdiv"; "<<"; ">>"; "mod"; "rem"];
    200,	Xfx,	["**"];
    200,	Xfy,	["^"];
    200,	Fy,	["+"; "-"; "\\"];
(*    100,	Yfx,	["."];*)
    1,	Fx,	["$"];
  ]

let opsmap = ref []

let rec update x v = function
  | [] -> [x,v]
  | (k,_)::xs when x=k -> (x,v)::xs
  | (k,v1)::xs -> (k,v1)::update x v xs

let opadd(p,o,(ls : string list)) =
  List.iter(fun (op:string) ->
    let map = (op,p)::List.assoc o !opsmap in
    opsmap := update o map !opsmap
  ) ls

let init_ops() =
  opsmap := [Xfx,[];Yfx,[];Fx,[];Fy,[];Xfy,[];Xf,[];Yf,[]];
  List.iter opadd ops

let () = init_ops()

let show_opp (op,p) = Printf.sprintf "%S,%d" op p

let show_opps () =
  !opsmap |> List.iter(fun (o,ls)->
    Printf.printf "%s : " (show_o o);
    let ls = List.map show_opp ls in
    Printf.printf "[%s]\n" (String.concat "; " ls)
  )

let opn o op =
  try List.assoc op (List.assoc o !opsmap)
  with _ -> -1

let opnXfy op =
  try List.assoc op (List.assoc Xfy !opsmap)
  with _ -> opn Xfx op

let opnXf op =
  try List.assoc op (List.assoc Xf !opsmap)
  with _ -> opn Yf op

let opnFx op =
  try List.assoc op (List.assoc Fx !opsmap)
  with _ -> opn Fy op

let is_lower x =
  if x = "" then false else
  let c = Char.code (String.get x 0) in
  (c >= Char.code 'a' && c <= Char.code 'z')

let show_atom (i,x) =
  if is_lower x then i ^ x else Printf.sprintf "%s'%s'" i (String.escaped x)

let rec show1 = function
  | Atom(x)               -> show_atom x
  | Number(i,n) -> i^n
  | Str(i,x)              -> Printf.sprintf "%s%S" i x
  | Pred((i,"[]"), xs)    -> Printf.sprintf "%s[%s]" i(show1s xs)
  | Pred(x, xs)           -> Printf.sprintf "%s([%s])" (show_atom x) (show1s xs)
  | Pre((i,x), xs)        -> Printf.sprintf "pre(%s%s,%s)" i x (show1 xs)
  | Post(xs, (i,"."))     -> Printf.sprintf "%s%s.\n" i (show1 xs)
  | Post(xs, x)           -> Printf.sprintf "post(%s,%s)" (show1 xs) (show_atom x)
  | Bin(t1, (i,","), t2)  -> Printf.sprintf "bin(%s%s<,> %s)" (show1 t1) i (show1 t2)
  | Bin(t1, (i,x), t2)    -> Printf.sprintf "bin(%s<bin %s%s> %s)"  (show1 t1) i x (show1 t2)
  | Var((i,x))            -> i ^ x
  | Nil(i)                -> i ^ "nil"
  | Cons(x,i,y)             -> Printf.sprintf "cons(%s,%s%s)" (show1 x) i (show1 y)
and show1s ls =
  String.concat ", " (List.map (fun e-> show1 e) ls)

let showbin = function
  | "," -> ", "
  | "!" -> "!"
  | x -> " " ^ x ^ " "


let rec show p = function
  | Bin(t1, (i,"@"), t2)  -> Printf.sprintf "%s %s%s"  (show 10000 t1) i (show 10000 t2)
  | Bin(t1, (i,x), t2)   when opn Yfx x > p ->
    let p2 = opn Yfx x in
    Printf.sprintf "(%s%s%s%s)"  (show p2 t1) i(showbin x) (show p2 t2)
  | Bin(t1, (i,x), t2)   when opn Yfx x >= 0 ->
    let p2 = opn Yfx x in
    Printf.sprintf "%s%s%s%s" (show p2 t1) i(showbin x) (show (p2-1) t2)
  | Bin(t1, (i,x), t2)   when opnXfy x >= p ->
    let p2 = opnXfy x in
    Printf.sprintf "(%s%s%s%s)"  (show p2 t1) i(showbin x) (show p2 t2)
  | Bin(t1, (i,x), t2)   when opnXfy x >= 0 ->
    let p2 = opnXfy x in
    Printf.sprintf "%s%s%s%s" (show p2 t1) i(showbin x) (show (p2+1) t2)
  | Atom(i,"!")           -> i^"!"
  | Atom(i,"[]")          -> i^"[]"
  | Atom(x)               -> show_atom x
  | Number(i,n)         -> i^n
  | Str(i,x)            -> Printf.sprintf "%s%S" i x
  | Pred((i,"[]"), xs)       -> Printf.sprintf "%s[%s]" i(shows xs)
  | Pred((i,"{}"), xs)       -> Printf.sprintf "%s{%s}" i(shows xs)
  | Pred(x, xs)       -> Printf.sprintf "%s(%s)" (show_atom x) (shows xs)
  | Pre((i,x), xs) when opnFx x > p      -> let p = opnFx x in Printf.sprintf "(%s%s %s)" i x (show p xs)
  | Pre((i,x), xs) when opnFx x >= 0      -> let p = opnFx x in Printf.sprintf "%s%s %s" i x (show p xs)
  | Pre((i,x), xs)      ->  Printf.sprintf "%s%s %s" i x (show p xs)
  | Post(xs,(i,"."))      -> Printf.sprintf "%s%s.\n" i (show p xs)
  | Post(xs,x)       -> Printf.sprintf "%s(%s)" (show p xs) (show_atom x)
  | Bin(t1, (i,","), t2)    -> Printf.sprintf "%s%s, %s"  (show p t1) i (show p t2)
  | Bin(t1, (i,x), t2)      -> Printf.sprintf "%s %s%s %s"  (show p t1) i x (show p t2)
  | Var(i,x)                -> i^x
  | Nil(i) -> i
  | Cons(x,i,y) -> Printf.sprintf "%s %s%s" (show p x)i (show p y)
and shows ls =
  String.concat ", " (List.map (fun e-> show ((opn Xfy ",")) e) ls)

let opn o op =
  try List.assoc op (List.assoc o !opsmap)
  with _ -> 10001

let infixrs op =
  try List.assoc op (List.assoc Xfy !opsmap)
  with _ ->
  (try List.assoc op (List.assoc Xfx !opsmap)
  with _ -> 10001)

let infixs op =
  try List.assoc op (List.assoc Yfx !opsmap)
  with _ -> 10001

let postfixs op =
  try List.assoc op (List.assoc Xf !opsmap)
  with _ -> opn Yf op

let prefixs op =
  try List.assoc op (List.assoc Fx !opsmap)
  with _ -> opn Fy op

let show = show 10002

let rec exp (p:int) ((a,b) as ass) =
    (*Printf.printf "exp %d (%s,%s)\n" p (show1 a) (show1 b);
    flush_all();*)
    match ass with
			| (Nil(i), Cons(Cons(x,ci,y),ci2, zs)) -> (* 順番入れ替え *)
				let (y, ys)  = exp(10000)(Nil(i), Cons(x,ci,y)) in
				exp(p)(y,zs)
			| (Nil(i), Cons(Pred(x,y),ci, zs)) -> (* predの中身を書き換え *)
				let y = List.map (fun y ->
          let (y, ys)  = exp(10000)(Nil(i), y) in
          y
        ) y in
				exp(p)(Pred(x,y),zs)
			| (Nil(i), Cons(Post(y,(x,pi)),ci, zs)) -> (* postの中身を書き換え *)
				let (y,_) = exp(10000)(Nil(i), y) in
				exp(p)(Post(y,(ci^x,pi)),zs)
			| (Nil(i), Cons(Atom(i2,op),ci, xs)) when  (p > prefixs(op)) -> (* 前置演算子 *)
				let (y, ys) = exp(prefixs(op))((Nil(i), xs)) in
				exp(p)(Pre((i2,op),y),ys)
			| (Nil(_), Cons(x, ci,xs)) -> exp(p)(x, xs) (* 何でもない *)

			| (x, Cons(Atom(i,op),ci, xs)) when  (p > infixs(op)) -> (* 中置演算子 *)
				let (y, ys) = exp(infixs(op))((Nil(xe), xs)) in
				exp(p)(Bin(x, (i,op), y), ys)
			| (x, Cons(Atom(i,op),ci, xs)) when  (p >=infixrs(op))-> (* 中置演算子 *)
				let (y, ys) = exp(infixrs(op))(Nil(xe), xs) in
				exp(p)(Bin(x, (i,op), y), ys)
			| (x, Cons(Atom(i,op),ci, xs)) when  (p >= postfixs(op)) -> (* 後置演算子 *)
				exp(p)(Post(x,(i,op)),xs)
			| (Nil(_), xs) -> ass
			| (x, xs) when (xs = Nil(xe)) -> ass
			| (x, xs) when  (p >= 10000) ->
				let (y, ys) = exp(10000)((Nil(xe), xs)) in
				begin match y with
        | Nil(i) -> (x, xs)
        | _ -> exp(10000)((Bin(x, (xe,"@"), y), ys))
				end                 
			| _ -> ass

let opconvert e =
  (*Printf.printf "koko %s\n" (show1 e);*)
  flush_all();
  let (a,b) = exp 10000 (Nil(xe),e) in
  (*Printf.printf "a:%s\n" (show1 a);*)
  (*Printf.printf "b:%s\n" (show1 b);*)
  a
