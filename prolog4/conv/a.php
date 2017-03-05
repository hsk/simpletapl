#!/usr/bin/env php
<?php
$dt = $argv[1];

function system1($cmd) {
  system($cmd,$rc);
  return $rc;
}

`./conv/conv ../prolog3/$dt.pl > $dt.pl`;
$s = file_get_contents("$dt.pl");

$s = preg_replace("/^ /m","",$s);

if(preg_match("{/-}",$s,$m)>0)
	$s = ":- discontiguous((/-)/2).\n".$s;
if(preg_match("{\\-}",$s,$m)>0)
	$s = ":- discontiguous((\\-)/2).\n".$s;

file_put_contents("$dt.pl",$s);

if(system1("swipl $dt.pl > results/{$dt}_expected.txt")!=0)exit(-1);
#if(system1("diff expected.txt result.txt")!=0)exit(-1);
#system1("diff expected.txt result.txt");
