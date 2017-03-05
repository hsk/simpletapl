# simple tapl pl

これはなに？

TAPLのサンプルコードを単純化してPrologに移植したものです。


# ファイル

- 第Ⅰ部 型無しの計算体系
    - [arith](arith.pl) 型無し算術式 bool+nat(３,4章)
    - [fulluntyped](fulluntyped.pl) フル型無しラムダ計算 bool+nat+float+λ+let+record(5,6章)
    - [untyped](untyped.pl) 型無しラムダ計算 λ (7章)
- 第Ⅱ部 単純型
    - [tyarith](tyarith.pl) 単純型付算術演算 bool+nat+単純型(8章)
    - [fullsimple](fullsimple.pl) フル単純型付ラムダ計算 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+単純型(9,11章)
    - [simplebool](simplebool.pl) 単純型付ラムダ計算+bool bool+nat+λ+単純型(10章)
    - [fullref](fullref.pl) フル単純型付ラムダ計算+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+ref+top+bot+source+sink+単純型(13,18章)
    - [fullerror](fullerror.pl) フル単純型付ラムダ計算+エラー bool+λ+top+bot+try error+単純型(14章)
- 第Ⅲ部 部分型付け
    - [rcdsubbot](rcdsubbot.pl) 単純部分型付ラムダ計算レコードbot λ+top+bot+record+単純部分型 (15,16章)
    - [fullsub](fullsub.pl) フル単純部分型付きラムダ計算 botなし bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+単純部分型 (15章)
    - [bot](bot) 単純部分型付きラムダ計算+bot λ+top+bot+単純部分型(16章)
    - [joinsub](joinsub.pl) (16章) 実装なし？
- 第Ⅳ部 再帰型
    - [fullisorec](fullisorec.pl) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+fold+unfold+単純再帰型(20章)
    - [fullequirec](fullequirec.pl) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+単純再帰型(20章)
    - [equirec](equirec.pl) 再帰型 λ+rec+単純再帰型(21章)
- 第Ⅴ部 多相性
    - [reconbase](reconbase.pl) 型再構築のベース bool+nat+λ+単純型(22章)
    - [recon](recon.pl) 型再構築 bool+nat+λ+型推論(22章)
    - [fullrecon](fullrecon.pl) フル型再構築 bool+nat+λ+let+型推論(22章)
    - [fullpoly](fullpoly.pl) フル全称型、存在型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+all+some(23,24章)
    - [fullfsub](fullfsub.pl) フルF<: 有界量化 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some(26,28章)
    - [fullfsubref](fullfsubref.pl) フルF<: 有界量化+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all (27章)
    - [purefsub](purefsub.pl) 有界量化 λ+top+<:(28章)
- 第Ⅵ部 高階の型システム
    - [fomega](fomega.pl) +kind
    - [fullomega](fullomega.pl) フル型演算とカインド、高階多相 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+ref+all+some+kind(29,30章)
    - [fullfomsub](fullfomsub.pl) フル有界量化サブ bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some+kind(26,31章)
    - [fomsub](fomsub.pl) 高階部分型付け λ+top+<:+all+kind(31章)
    - [fullfomsubref](fullfomsubref.pl) フル有界量化サブ+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all+some+kind+import
    - [fullupdate](fullupdate.pl) フル純粋関数的オブジェクト 書き換え可能レコード bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+top+<:+all+some+kind+variance(32章)
