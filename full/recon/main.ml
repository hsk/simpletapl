open Syntax
open Core

let parseFile filename =
  let fp = open_in filename in
  let m = Parser.p Lexer.main (Lexing.from_channel fp) in
  Parsing.clear_parser();
  close_in fp;
  m

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t

let _ = 
  let filename = ref "" in
  Arg.parse [] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
  List.fold_left (fun (g,nextuvar,constr) -> function
    | Eval(m)->
      let (t,nextuvar',constr_t) = typeof g nextuvar constr m in
      let m = eval g m in
      Printf.printf "%s : %s\n" (show m) (show_t t);
      (g,nextuvar',constr_t)
    | Bind(x,bind) ->
      Printf.printf "%s%s\n" x (show_bind g bind);
      ((x,bind)::g, uvargen, constr)
  ) ([],uvargen,[]) (parseFile !filename) 
