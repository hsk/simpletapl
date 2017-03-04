<?php

foreach(explode("\n",file_get_contents("aa.txt")) as $d) {
  echo "cp fullerror/Makefile $d/.\n";
}


