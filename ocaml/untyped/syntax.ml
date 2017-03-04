type m =
  | MVar of string
  | MAbs of string * m
  | MApp of m * m

type b =
  | BName 

type c =
  | Eval of m
  | Bind of string * b

let rec show = function
  | MAbs(x, m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | m -> "(" ^ show m ^ ")"

let rec subst x m = function
  | MVar(x1) when x = x1 -> m
  | MApp(m1, m2) -> MApp(subst x m m1, subst x m m2)
  | MAbs(x1, m2) when x<>x1 -> MAbs(x1, subst x m m2)
  | m -> m

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)
