# 型無し計算
# 単純型
# 部分型
# 参照
# エラー
# 再帰型
# 型再構築
# 多相型
# 有界型
# カインド

<?php

$arr=array();
foreach(explode("\n",file_get_contents("aa.txt")) as $d) {
    $name = "$d/core.ml";
    $s = file_get_contents($name);
    preg_replace_callback("/^(let\s+(rec\s+)?|and\s+)(\w+)/m", function($m) use (&$arr,$name) {
        if(!isset($arr[$m[3]])) $arr[$m[3]]=array();
        $name = preg_replace("/\/core.ml/","",$name);
        $arr[$m[3]][]=$name;
    },$s);
}

$fnames = array (
  'n' => "整数値チェック",
  'v' => "値チェック",
  'eval1' => "1回評価",
  'eval' => "評価",
  'typeof' => "型検査",
  'subtype' => "部分型検査",
  'compute' => "計算",
  'simplify' => "シンプル化",
  'teq' => "型等価",
  'evalbinding' => "バインド評価",
  'istabb' => "型バインドチェック",
  'gettabb' => "型バインド取得",
  'extendstore' => "ストア拡張",
  'lookuploc' => "ストア位置検索",
  'updatestore' => "ストア更新",
  'join' => "ジョイン",
  'meet' => "ミート",
  'uvargen' => "",
  'recon' => "型再構築",
  'substinty' => "置き換えてぃ",
  'applysubst' => "置き換え適用",
  'substinconstr' => "置き換え",
  'occursin' => "出現検査",
  'unify' => "単一化",
  'prconstr' => "",
  'promote' => "型昇格",
  'lcst' => "",
  'kindof' => "カインド取得",
  'checkkindstar' => "\*検査",
);
$i = 0;
foreach($arr as $k=>$n) {
    $i++;
    $full=array();
    $pure=array();
    foreach($n as $j)
        if(preg_match("/full/",$j)>0) $full[]=$j; else $pure[] = $j;
    printf("## $i %s %s\n\n    %s\n    %s\n\n", $k, $fnames[$k],implode(",",$pure),implode(",", $full));
}
