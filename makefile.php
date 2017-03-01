<?php

$dt = file_get_contents("aa.txt");
$dt = explode("\n", $dt);

foreach($dt as $d) {
  printf("#\tswipl %s.pl > results/%s_result.txt\n", $d, $d);
  printf("#\tdiff results/%s_result.txt results/%s_expected.txt\n", $d, $d);
}


foreach($dt as $d) {
  printf("#\tswipl %s.pl > results/%s_expected.txt\n", $d, $d);
}

