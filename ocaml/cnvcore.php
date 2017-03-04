<?php

foreach(explode("\n",file_get_contents("aa.txt")) as $d) {
    $name = "$d/core.ml";
    $s = file_get_contents($name);
    $s = preg_replace('/^\n+/s','', $s);

    $s = preg_replace('/let rec  m =\n  match m with\n/s',"let rec  = function\n", $s);
    $s = preg_replace('/let rec eval1 a m =\n  match m with\n/s',"let rec eval1 a = function\n", $s);
    $s = preg_replace('/let rec typeof a m =\n  match m with\n/s',"let rec typeof a = function\n", $s);
    $s = preg_replace('/let rec kindof a t =\n  match t with\n/s',"let rec kindof a = function\n", $s);
    $s = preg_replace('/let rec eval1 a store m =\n  match m with\n/s',"let rec eval1 a store = function\n", $s);
    $s = preg_replace('/let evalbinding a b =\n  match b with\n/s',"let evalbinding a = function\n", $s);
    $s = preg_replace('/let evalbinding a store b =\n  match b with\n/s',"let evalbinding a store = function\n", $s);
    file_put_contents($name, $s);
}
