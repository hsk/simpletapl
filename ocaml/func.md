# 1. 型無し計算

## 1.1 n 整数値チェック

    arith,tyarith,reconbase,recon
    fulluntyped,fullsimple,fullref,fullsub,fullequirec,fullisorec,fullrecon,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 1.2 v 値チェック

    arith,untyped,tyarith,simplebool,bot,rcdsubbot,equirec,reconbase,recon,purefsub,fomega,fomsub,joinexercise,letexercise
    fulluntyped,fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullrecon,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 1.3 eval1 1回評価

    arith,untyped,tyarith,simplebool,bot,rcdsubbot,equirec,reconbase,recon,purefsub,fomega,fomsub,joinexercise,letexercise
    fulluntyped,fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullrecon,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 1.4 eval 評価

    arith,untyped,tyarith,simplebool,bot,rcdsubbot,equirec,reconbase,recon,purefsub,fomega,fomsub,joinexercise,letexercise
    fulluntyped,fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullrecon,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 1.5 evalbinding バインド評価

    fulluntyped,fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

# 2. 単純型

## 2.1 typeof 型検査

    tyarith,simplebool,bot,rcdsubbot,equirec,reconbase,recon,purefsub,fomega,fomsub,joinexercise,letexercise
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullrecon,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 2.2 istabb 型バインドチェック
    
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 2.3 gettabb 型バインド取得
    
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 2.4 compute 型計算

    equirec,fomega,fomsub
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 2.5 simplify 型シンプル化

    equirec,fomega,fomsub
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

## 2.6 teq 型等価

    equirec,equirec,fomega,fomsub
    fullsimple,fullref,fullerror,fullsub,fullequirec,fullequirec,fullisorec,fullpoly,fullfsub,fullfsubref,fullomega,fullfomsub,fullfomsubref,fullupdate

# 3. 参照

## 3.1 extendstore ストア拡張
    
    fullref,fullfsubref,fullomega,fullfomsubref

## 3.2 lookuploc ストア位置検索
    
    fullref,fullfsubref,fullomega,fullfomsubref

## 3.3 updatestore ストア更新
    
    fullref,fullfsubref,fullomega,fullfomsubref

# 4. 部分型

## 4.1 subtype 部分型検査

    bot,rcdsubbot,purefsub,fomsub,joinexercise
    fullref,fullerror,fullsub,fullfsub,fullfsubref,fullfomsub,fullfomsubref,fullupdate

## 4.2 join 結び

    joinexercise
    fullref,fullerror,fullsub,fullfsub,fullfsubref,fullfomsub,fullfomsubref,fullupdate

## 4.3 meet 交わり

    joinexercise
    fullref,fullerror,fullsub,fullfsub,fullfsubref,fullfomsub,fullfomsubref,fullupdate

# 5. 型再構築

## 5.1 uvargen 

    recon fullrecon

## 5.2 recon 型再構築

    recon fullrecon

## 5.3 substinty 型置き換え

    recon fullrecon

## 5.4 applysubst 置き換え適用

    recon fullrecon

## 5.5 substinconstr 定数置き換え

    recon fullrecon

## 5.6 occursin 出現検査

    recon fullrecon

## 5.7 unify 単一化

    recon fullrecon

# 6. 有界型 F<:

## 6.1 promote 型昇格

    purefsub,fomsub
    fullfsub,fullfsubref,fullfomsub,fullfomsubref,fullupdate

## 6.2 lcst 

    purefsub,fomsub
    fullfsub,fullfsubref,fullfomsub,fullfomsubref,fullupdate

# 6. カインド、高階多相 Fω

## 6.1 kindof カインド取得

    fomega,fomsub
    fullomega,fullfomsub,fullfomsubref,fullupdate

## 6.2 checkkindstar \*検査

    fomega,fomsub
    fullomega,fullfomsub,fullfomsubref,fullupdate
