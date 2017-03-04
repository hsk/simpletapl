<?php

foreach(explode("\n",file_get_contents("aa.txt")) as $d) {
    $name = "$d/main.ml";
    $s = file_get_contents($name);
    $s = preg_replace('/^\n/s','', $s);
    $s = preg_replace('/^let \(\)/m','let _', $s);
    $s = preg_replace('/\\|> ignore\s*$/s', "\n", $s);

    $s = preg_replace('/let parseFile.*?\nlet/s',"let parseFile filename =
  let fp = open_in filename in
  let m = Parser.p Lexer.main (Lexing.from_channel fp) in
  Parsing.clear_parser();
  close_in fp;
  m

let",$s);
    file_put_contents($name, $s);
}
