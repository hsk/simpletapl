# TAPL19 Fetherweight Java
## 図19-1.Featherweight Java (構文と部分型付け)

    構文

    CL ::=                     クラス宣言：
    　class C extends C {[C f;] K [M] }

    K ::=              コンストラクタ宣言：
    　C([C f]) { super([f]); [this.f=f;] }

    M ::=                    メソッド宣言：
    　C m([C m]) { return t; }

    t ::=                              項：
    　x                                変数
    　t.f                              フィールドアクセス
    　t.m([t])                         メソッド呼び出し
    　new C([t])                       オブジェクト生成
    　(C) t                            キャスト

    v ::=                              値：
    　new C([v])                       オブジェクト生成

    部分型付け規則 Γ ⊢ C <: D

    C <: C

    C <: D　　D <: E
    ———————————
    C <: E

    CT(C) = class C extends D {…}
    ————————————————
    C <: D

## 図19-2.Fetherweight Java (補助的な定義)

    フィールドの探索 fields(C)= [C f]

    fields(Object) = •

    CT(C) = class C extends D {[C f;] K [M]}
    fields(D) = [D g]
    —————————————————————
    fields(C) = [D g],[C f]


    メソッドの型の探索 mtype(m,C) = [C] -> C

    CT(C) = class C extends D {[C f;] K [M]}
    B m ([B x]) {return t;} ∈ [M]
    —————————————————————
    mtype(m,C) = [B] -> B

    CT(C) = class C extends D {[C f;] K [M]}
    mは[M]の中で定義されていない
    —————————————————————
    mtype(m,C) = mtype(m,D)


    メソッドの本体の探索 mbody(m,C) = ([x],t)

    CT(C) = class C extends D {[C f;] K [M]}
    B m ([B x]) {return t;} ∈ [M]
    —————————————————————
    mbody(m, C) = ([x],t)

    CT(C) = class C extends D{[C f;] K [M]}
    m は [M] の中で定義されていない
    —————————————————————
    mbody(m,C)=mbody(m,D)


    メソッドの正当なオーバーライド override(m, D, [C]->C0)

    mtype(m,D) = [D]->D0 ならば、 [C] = [D] かつ C0 = D0
    ———————————————————————————
    override(m, D, [C] -> C0)

## 図19-3.Fetherweight Java (評価)

    評価 t ==> t’

    fields(C) = [C f]
    ————————————————————— (E-ProjNew)
    (new C([v])).fi ==> vi

    mbody(m,C) = ([x], t0)
    ————————————————————— (E-InvkNew)
    (new C([v])).m([u])
    ==> [[x]->[u],this->new C([v])]t0

    C <: D
    ————————————————————— (E-CastNew)
    (D)(new C([v])) ==> new C([v])

    t0 ==> t0’
    ————————————————————— (E-Field)
    t0.f ==> t0’.f

    t0 ==> t0’
    ————————————————————— (E-Invk-Recv)
    t0.m([t]) ==> t0’.m([t])

    ti ==> ti’
    ————————————————————— (E-Invk-Arg)
    v0.m([v],ti,[t]) ==> v0.m([v],ti’,[t])

    ti ==> ti’
    ————————————————————— (E-New-Arg)
    new C([v],ti,[t]) ==> new C([v],ti’,[t])

    t0 ==> t0’
    ————————————————————— (E-Cast)
    (C)t0 ==> (C)t0’

## 図19-4.Fetherweight Java (型付け)

    項の型付け Γ ⊢ t : C

    x : C ∈ Γ
    —————————————————— (T-Var)
    Γ ⊢ t : C

    Γ ⊢ t0 : C0   fields(C0) = [C f]
    —————————————————— (T-Field)
    Γ ⊢ t0.fi : Ci

    Γ ⊢ t0 : C0
    mtype(m, C0) = [D] -> C
    Γ ⊢ [t] : [C]      [C] <: [D]
    —————————————————— (T-Invk)
    Γ ⊢ t0.m([t] : C

    fields(C) = [D f]
    Γ ⊢ [t] : [C]      [C] <: [D]
    —————————————————— (T-New)
    Γ ⊢ new C([t]) : C

    Γ ⊢ t0 : D     D <: C
    —————————————————— (T-UCast)
    Γ ⊢ (C)(t0) : C

    Γ ⊢ t0 : D     C <: D    C =/= D
    —————————————————— (T-DCast)
    Γ ⊢ (C)(t0) : C

    Γ ⊢ t0 : D     C /<: D    C /<: D
    愚かさの警告
    —————————————————— (T-SCast)
    Γ ⊢ (C)(t0) : C

    メソッドの型付け M OK in C

    [x]:[C],this:C ⊢ t0:E0    E0 <: C0
    CT(C) = class C extends D {…}
    override(m,D,[C]->C0)
    ——————————————————
    C0 m ([C x]) { return t0; } OK in C

    クラスの型付け C OK

    K=C([D g],[C f])
    {super([g]); this.f = f; }
    fields(D) = [D g]    [M] OK in C
    ————————————————
    class C extends D {[C f;] K M} OK

## 定義19.5.3. FJの評価文脈

  定義 19.5.3. FJの評価文脈の集合は以下のように定義される。

    E ::= 評価文脈：
    　[]               穴
    　E.f              フィールド参照
    　E.m([t])         メソッド呼び出し(レシーバ)
    　E.m([v],E,[t])   メソッド呼び出し(引数)
    　new C([v],E,[t]) オブジェクト生成(引数)
    　(C)E             キャスト
