# simple tapl pl

これはなに？

TAPLのサンプルコードを単純化してPrologに移植したものです。

# ファイル

- 第Ⅰ部 型無しの計算体系
    - [ ] 29 [arith](arith.pl) 型無し算術式 bool+nat(３,4章)
    - [ ] 28 [fulluntyped](fulluntyped.pl) フル型無しラムダ計算 bool+nat+float+λ+let+record(5,6章)
    - [ ] 27 [untyped](untyped.pl) 型無しラムダ計算 λ (7章)
- 第Ⅱ部 単純型
    - [ ] 26 [tyarith](tyarith.pl) 単純型付算術演算 bool+nat+単純型(8章)
    - [ ] 25 [fullsimple](fullsimple.pl) フル単純型付ラムダ計算 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+単純型(9,11章)
    - [ ] 24 [simplebool](simplebool.pl) 単純型付ラムダ計算+bool bool+nat+λ+単純型(10章)
    - [ ] 23 [fullref](fullref.pl) フル単純型付ラムダ計算+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+ref+top+bot+source+sink+単純型(13,18章)
    - [ ] 22 [fullerror](fullerror.pl) フル単純型付ラムダ計算+エラー bool+λ+top+bot+try error+単純型(14章)
- 第Ⅲ部 部分型付け
    - [ ] 21 [rcdsubbot](rcdsubbot.pl) 単純部分型付ラムダ計算レコードbot λ+top+bot+record+単純部分型 (15,16章)
    - [ ] 20 [fullsub](fullsub.pl) フル単純部分型付きラムダ計算 botなし bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+単純部分型 (15章)
    - [ ] 19 [bot](bot.pl) 単純部分型付きラムダ計算+bot λ+top+bot+単純部分型(16章)
    - [ ] 18 [joinsub](joinsub.pl) (16章) 実装なし？
    - [ ] 17 [joinexercise](joinexercise.pl) 
- 第Ⅳ部 再帰型
    - [ ] 16 [ful+lisorec](fullisorec.pl) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+fold+unfold+単純再帰型(20章)
    - [ ] 15 [fullequirec](fullequirec.pl) フル再帰型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+rec+単純再帰型(20章)
    - [ ] 14 [equirec](equirec.pl) 再帰型 λ+rec+単純再帰型(21章)
- 第Ⅴ部 多相性
    - [ ] 13 [reconbase](reconbase.pl) 型再構築のベース bool+nat+λ+単純型(22章)
    - [ ] 12 [recon](recon.pl) 型再構築 bool+nat+λ+型推論(22章)
    - [ ] 11 [fullrecon](fullrecon.pl) フル型再構築 bool+nat+λ+let+型推論(22章)
    - [ ] 10 [fullpoly](fullpoly.pl) フル全称型、存在型 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+all+some(23,24章)
    - [ ] 9 [fullfsub](fullfsub.pl) フルF<: 有界量化 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some(26,28章)
    - [ ] 8 [fullfsubref](fullfsubref.pl) フルF<: 有界量化+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all (27章)
    - [ ] 7 [purefsub](purefsub.pl) 有界量化 λ+top+<:(28章)
- 第Ⅵ部 高階の型システム
    - [ ] 6 [fomega](fomega.pl) +kind
    - [ ] 5 [fullomega](fullomega.pl) フル型演算とカインド、高階多相 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+ref+all+some+kind(29,30章)
    - [ ] 4 [fullfomsub](fullfomsub.pl) フル有界量化サブ bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+top+<:+all+some+kind(26,31章)
    - [ ] 3 [fomsub](fomsub.pl) 高階部分型付け λ+top+<:+all+kind(31章)
    - [ ] 2 [fullfomsubref](fullfomsubref.pl) フル有界量化サブ+参照 bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+record+case of+try error+ref+top+bot+<:+source+sink+all+some+kind+import
    - [ ] 1 [fullupdate](fullupdate.pl) フル純粋関数的オブジェクト 書き換え可能レコード bool+nat+unit+float+string+λ+let+letrec+fix+inert+as+top+<:+all+some+kind+variance(32章)

# TODO

    - [ ] tagの表現を変える。
    - [ ] fullequirecのwrite(ok)を消す。
    - [ ] equirecのコメントをよくする。
