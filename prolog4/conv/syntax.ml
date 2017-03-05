type t =
  | Atom of string
  | Number of string
  | Str of string
  | Pred of string * t list
  | Post of t * string
  | Pre of string * t
  | Bin of t * string * t
  | Var of string
  | Cons of t * t
  | Nil

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
    1200,	Xfx,	["-->"; ":-"];
    1190,	Fx,	[":-"; "?-"];
    1180,	Xf,	["."];(* added *)
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

let show_atom x =
  if is_lower x then x else Printf.sprintf "'%s'" (String.escaped x)

let rec show1 = function
  | Atom(x)           -> show_atom x
  | Number(n)         -> n
  | Str(x)            -> Printf.sprintf "%S" x
  | Pred("[]", xs)    -> Printf.sprintf "[%s]" (show1s xs)
  | Pred(x, xs)       -> Printf.sprintf "%s([%s])" (show_atom x) (show1s xs)
  | Pre(x, xs)       -> Printf.sprintf "pre(%s,%s)" x (show1 xs)
  | Post(xs,".")      -> Printf.sprintf "%s.\n" (show1 xs)
  | Post(xs,x)       -> Printf.sprintf "post(%s,%s)" (show1 xs) (show_atom x)
  | Bin(t1, ",", t2)    -> Printf.sprintf "bin(%s<,> %s)"  (show1 t1) (show1 t2)
  | Bin(t1, x, t2)    -> Printf.sprintf "bin(%s<bin %s> %s)"  (show1 t1)  x (show1 t2)
  | Var(x)            -> x
  | Nil               -> "nil"
  | Cons(x,y)         -> Printf.sprintf "cons(%s,%s)" (show1 x) (show1 y)
and show1s ls =
  String.concat ", " (List.map (fun e-> show1 e) ls)

let showbin = function
  | "," -> ", "
  | "!" -> "!"
  | x -> " " ^ x ^ " "


let rec show p = function
  | Bin(t1, "@", t2)  -> Printf.sprintf "%s %s"  (show 10000 t1) (show 10000 t2)
  | Bin(t1, x, t2)   when opn Yfx x > p ->
    let p2 = opn Yfx x in
    Printf.sprintf "(%s%s%s)"  (show p2 t1) (showbin x) (show p2 t2)
  | Bin(t1, x, t2)   when opn Yfx x >= 0 ->
    let p2 = opn Yfx x in
    Printf.sprintf "%s%s%s" (show p2 t1) (showbin x) (show (p2-1) t2)
  | Bin(t1, x, t2)   when opnXfy x >= p ->
    let p2 = opnXfy x in
    Printf.sprintf "(%s%s%s)"  (show p2 t1) (showbin x) (show p2 t2)
  | Bin(t1, x, t2)   when opnXfy x >= 0 ->
    let p2 = opnXfy x in
    Printf.sprintf "%s%s%s" (show p2 t1) (showbin x) (show (p2+1) t2)
  | Atom("!")           -> "!"
  | Atom("[]")          -> "[]"
  | Atom(x)           -> show_atom x
  | Number(n)         -> n
  | Str(x)            -> Printf.sprintf "%S" x
  | Pred("[]", xs)       -> Printf.sprintf "[%s]" (shows xs)
  | Pred("{}", xs)       -> Printf.sprintf "{%s}" (shows xs)
  | Pred(x, xs)       -> Printf.sprintf "%s(%s)" (show_atom x) (shows xs)
  | Pre(x, xs) when opnFx x > p      -> let p = opnFx x in Printf.sprintf "(%s %s)" x (show p xs)
  | Pre(x, xs) when opnFx x >= 0      -> let p = opnFx x in Printf.sprintf "%s %s" x (show p xs)
  | Pre(x, xs)      ->  Printf.sprintf "%s %s" x (show p xs)
  | Post(xs,".")      -> Printf.sprintf "%s.\n" (show p xs)
  | Post(xs,x)       -> Printf.sprintf "%s(%s)" (show p xs) (show_atom x)
  | Bin(t1, ",", t2)    -> Printf.sprintf "%s, %s"  (show p t1) (show p t2)
  | Bin(t1, x, t2)    -> Printf.sprintf "%s %s %s"  (show p t1)  x (show p t2)
  | Var(x)            -> x
  | Nil -> "nil"
  | Cons(x,y) -> Printf.sprintf "cons(%s,%s)" (show p x) (show p y)
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
			| (Nil, Cons(Cons(x,y), zs)) ->
				let (y, ys)  = exp(10000)(Nil, Cons(x,y)) in
				exp(p)(y,zs)
			| (Nil, Cons(Pred(x,y), zs)) ->
				let y = List.map (fun y ->
          let (y, ys)  = exp(10000)(Nil, y) in
          y
        ) y in
				exp(p)(Pred(x,y),zs)
			| (Nil, Cons(Atom(op), xs)) when  (p > prefixs(op)) ->
				let (y, ys) = exp(prefixs(op))((Nil, xs)) in
				exp(p)(Pre(op,y),ys)
			| (Nil, Cons(x, xs)) -> exp(p)((x, xs))

			| (x, Cons(Atom(op), xs)) when  (p >= postfixs(op)) ->
				exp(p)(Post(x,op),xs)

			| (x, Cons(Atom(op), xs)) when  (p > infixs(op)) ->
				let (y, ys) = exp(infixs(op))((Nil, xs)) in
				exp(p)(Bin(x, op, y), ys)
			| (x, Cons(Atom(op), xs)) when  (p >=infixrs(op))->
				let (y, ys) = exp(infixrs(op))(Nil, xs) in
				exp(p)(Bin(x, op, y), ys)
			| (Nil, xs) -> ass
			| (x, xs) when (xs = Nil) -> ass
			| (x, xs) when  (p >= 10000) ->
				let (y, ys) = exp(10000)((Nil, xs)) in
				if (y <> Nil) then exp(10000)((Bin(x, "@", y), ys))
				else                 (x, xs)
			| _ -> ass

let opconvert e =
  (*Printf.printf "koko %s\n" (show1 e);*)
  flush_all();
  let (a,b) = exp 10000 (Nil,e) in
  (*Printf.printf "a:%s\n" (show1 a);*)
  (*Printf.printf "b:%s\n" (show1 b);*)
  a
