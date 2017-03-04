<?php

foreach(explode("\n",file_get_contents("aa.txt")) as $d) {
    $name = "$d/parser.mly";
    $s = file_get_contents($name);
    $s = preg_replace("/\s+\$/m","",$s);
    $s = preg_replace("/\n\n/s","\n",$s);
    $s = preg_replace("/\$/s","\n",$s);
    $s = preg_replace("/\\)\nlet/s",")\n\nlet",$s);
    $s = preg_replace("/%%/","%%\n",$s);
    $s = preg_replace('/\\bty_binder\\b/s',"b_t",$s);
    $s = preg_replace('/\\bbinder\\b/s',"b",$s);
    $s = preg_replace('/\\btype_\\b/s',"t",$s);
    $s = preg_replace('/\\bty\\b/s',"t",$s);
    $s = preg_replace('/ty_/s',"t_",$s);
    $s = preg_replace('/\\bo_kind\\b/s',"k_o",$s);
    $s = preg_replace('/\\bkind\\b/s',"k",$s);
    $s = preg_replace('/\\barrow_kind\\b/s',"k_arr",$s);
    $s = preg_replace('/\\ba_kind\\b/s',"k_a",$s);
    $s = preg_replace('/\\bo_type\\b/s',"t_o",$s);
    $s = preg_replace('/\\bapp_type\\b/s',"t_app",$s);
    $s = preg_replace('/\\barrow_type\\b/s',"t_arr",$s);
    $s = preg_replace('/\\ba_type\\b/s',"t_a",$s);
    $s = preg_replace('/\\bterm\\b/s',"m",$s);
    $s = preg_replace('/\\bapp_term\\b/s',"m_app",$s);
    $s = preg_replace('/\\bpath_term\\b/s',"m_path",$s);
    $s = preg_replace('/\\bterm_seq\\b/s',"m_seq",$s);
    $s = preg_replace('/\\bascribe_term\\b/s',"m_as",$s);
    $s = preg_replace('/\\ba_term\\b/s',"m_a",$s);
    $s = preg_replace('/\\bfield_types\\b/s',"t_fields",$s);
    $s = preg_replace('/\\bfield_type\\b/s',"t_field",$s);
    $s = preg_replace('/\\bne_field_types\\b/s',"t_fields_ne",$s);
    $s = preg_replace('/\\bfields\\b/s',"fields",$s);
    $s = preg_replace('/\\bfield\\b/s',"field",$s);
    $s = preg_replace('/\\bne_fields\\b/s',"fields_ne",$s);
    $s = preg_replace('/\n[^\n]*\|[^\n]*USCORE[^\n]*\n/s',"\n",$s);
    $s = preg_replace('/field/s',"fl",$s);
    $s = preg_replace('/ *-> */s'," -> ",$s);

    $s = preg_replace_callback('/^([a-z_0-9]*)\\s*(:|\|)\s*([A-Za-z_0-9 ]*?)\s*{/m',function($m){
        $r = sprintf("%-10s%s %-38s{",$m[1],$m[2],$m[3]);
        echo $r."\n";
        return $r;
    }, $s);
    file_put_contents($name, $s);
}
