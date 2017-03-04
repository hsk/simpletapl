# simple tapl

これはなに？

TAPLのサンプルコードを以下の考えの元でより単純に書き換えたものです。

- mliファイルを消去
- support.mlを消去
- 位置情報を構文木から削除
- ド・ブラン・インデックス化とα変換をやめてパーサを単純化
- ド・ブラン・インデックス化の削除に伴いシフト関連の処理を削除
- 置換処理で名前がかぶった場合には置換しないように修正
- パーサのトークン定義をまとめて圧縮
- パーサからコメントを削除
- パーサのアクション部分までを１行にまとめインデントを合わせて行数を圧縮
- 字句解析から位置情報取得機能を削除
- TyVarとTyIdはTyVarにまとめ、環境に値がない場合にTyIdのように動作するよう修正
- TmのプリフィックスをMに変え
- TyのプリフィックスをTに変え
- 印字処理を単純な文字列結合に変更しデータ定義の下に移動(インデントの機能がなくなった)
- できるだけ変数を介さず、ネストした関数呼び出しに変更
- addbinding,addname関数を消去しリスト::を使用
- match,try,funの()をbegin endに書き換え
- error関数をfailwithに書き換え
- main.mlの関数はparseFileのみにしてベタ書き
- Makefileはベタ書きすることで単純化

# ディレクトリ

unit as let tuple record case of list

- 第Ⅰ部 型無しの計算体系
    - [x] [arith](arith) 型無し算術式 bool+nat(３,4章)
    - [fulluntyped](fulluntyped) フル型無しラムダ計算 bool+nat+float+λ+let+record(5,6章)
    - [x] [untyped](untyped) 型無しラムダ計算 λ (7章)
- 第Ⅱ部 単純型
    - [tyarith](tyarith) 単純型付算術演算 bool+nat+単純型(8章)
    - [fullsimple](fullsimple) フル単純型付ラムダ計算 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+単純型(9,11章)
    - [simplebool](simplebool) 単純型付ラムダ計算+bool bool+nat+λ+単純型(10章)
    - [fullref](fullref) フル単純型付ラムダ計算+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+ref+top+bot+source+sink+単純型(13,18章)
    - [fullerror](fullerror) フル単純型付ラムダ計算+エラー bool+λ+top+bot+try error+単純型(14章)
- 第Ⅲ部 部分型付け
    - [rcdsubbot](rcdsubbot) 単純部分型付ラムダ計算レコードbot λ+top+bot+record+単純部分型 (15,16章)
    - [fullsub](fullsub) フル単純部分型付きラムダ計算 botなし bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+単純部分型 (15章)
    - [bot](bot) 単純部分型付きラムダ計算+bot λ+top+bot+単純部分型(16章)
    - [joinsub](joinsub) (16章) 実装なし？
- 第Ⅳ部 再帰型
    - [fullisorec](fullisorec) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+fold+unfold+単純再帰型(20章)
    - [fullequirec](fullequirec) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+単純再帰型(20章)
    - [x] [equirec](equirec) 再帰型 λ+rec+単純再帰型(21章)
- 第Ⅴ部 多相性
    - [x] [reconbase](reconbase) 型再構築のベース bool+nat+λ+単純型(22章)
    - [x] [recon](recon) 型再構築 bool+nat+λ+型推論(22章)
    - [x] [fullrecon](fullrecon) フル型再構築 bool+nat+λ+let+型推論(22章)
    - [x] [fullpoly](fullpoly) フル全称型、存在型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+all+some(23,24章)
    - [x] [fullfsub](fullfsub) フルF<: 有界量化 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some(26,28章)
    - [x] [fullfsubref](fullfsubref) フルF<: 有界量化+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all (27章)
    - [x] [purefsub](purefsub) 有界量化 λ+top+<:(28章)
- 第Ⅵ部 高階の型システム
    - [x] [fomega](fomega) +kind
    - [x] [fullomega](fullomega) フル型演算とカインド、高階多相 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+ref+all+some+kind(29,30章)
    - [x] [fullfomsub](fullfomsub) フル有界量化サブ bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some+kind(26,31章)
    - [x] [fomsub](fomsub) 高階部分型付け λ+top+<:+all+kind(31章)
    - [x] [fullfomsubref](fullfomsubref) フル有界量化サブ+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all+some+kind+import
    - [x] [fullupdate](fullupdate) フル純粋関数的オブジェクト 書き換え可能レコード bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+top+<:+all+some+kind+variance(32章)

joinexercise +record

fulluntyped.pl
farithsub
joinsub
fullsub
fomega
fullfsub
fullfomsub
fullsimple
fullref
