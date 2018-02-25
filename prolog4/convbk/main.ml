open Syntax

let parse_file filename = 
  let fp = open_in filename in
  Parser.top Lexer.token (Lexing.from_channel fp)

let parse str =
  Parser.top Lexer.token (Lexing.from_string str)

let debug = ref false

let run x =
  (*
    Printf.printf "parse start\n";flush_all();*)
    let ast = parse_file x in
    if !debug then Printf.printf "ast=%s\n" (show1 ast);
    (*
    Printf.printf "parse end\n";flush_all();*)
    let ast = opconvert ast in
    if !debug then Printf.printf "ast=%s\n" (show1 ast);
    (*let ast = Varconv.f ast in*)
    (*let ast = Conv.f ast in*)
    Printf.printf "%s\n" (show ast)

let () =
  Arg.parse
    ["-varbose",Arg.Unit (fun () -> debug := true), "show debug output"]
    (fun x -> run x)
    "Usage: compact filename1 filename2 ..."
