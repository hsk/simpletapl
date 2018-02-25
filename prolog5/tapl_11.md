# TAPL11 拡張
## 図11-1.非解釈基本型

  →A    λ→(図9-1)の拡張

    新しい構文形式

    T ::= … 型：
      A      基本型

## 図11-2.Unit型

  →Unit   λ→(図9-1)の拡張

    新しい構文形式

    t ::=       項：
      unit      定数unit

    v ::=       値：
      unit      定数unit

    T ::= …    型：
      Unit      Unit型

    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ unit : Unit                    (T-Unit)


    新しい派生形式

    t1;t2   def=    (λx:Unit.t2) t1
                    ただし x ∉ FV(t2)

## 図11-3.型指定

  →as   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …      項：
      t as T      型指定

    新しい評価規則 t ==> t’

    v1 as T ==> v1                             (E-Ascribe)

    t1 ==> t1’
    ————————————————————— (E-Ascribe1)
    t1 as T ==> t1’ as T


    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 : T
    ————————————————————— (T-Ascribe)
    Γ ⊢ t1 as T : T

## 図11-4.let束縛

  →let   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …            項：
      let x=t in t      let束縛


    新しい評価規則 t ==> t’

    let x=v1 in t2 ==> [x->v1] t2        (E-LetV)

    t1 ==> t1’
    —————————————————— (E-Let)
    let x=t1 in t2 ==> let x=t1’ in t2


    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 : T    Γ, x : T1 ⊢ t2 : T2
    —————————————————— (T-Let)
    Γ ⊢ let x=t1 in t2 : T2

## 図11-5.二つ組

  →×   λ→(図9-1)の拡張

    新しい構文形式

    t ::=         項：
      {t,t}       二つ組
      t.1         第一要素の射影
      t.2         第二要素の射影

    v ::=         値：
      {v,v}       二つ組値

    T ::= …      型：
      T1 × T2    直積型

    新しい評価規則 t ==> t’
    {v1,v2}.1 ==> v1                     (E-PairBeta1)

    {v1,v2}.2 ==> v2                     (E-PairBeta2)

    t1 ==> t1’
    —————————————————— (E-Proj1)
    t1.1 ==> t1’.1

    t1 ==> t1’
    —————————————————— (E-Proj2)
    t1.2 ==> t1’.2

    t1 ==> t1’
    —————————————————— (E-Pair1)
    {t1,t2} ==> {t1’,t2}

    t2 ==> t2’
    —————————————————— (E-Pair2)
    {v1,t2} ==> {v1,t2’}


    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 : T1    Γ ⊢ t2 : T2
    —————————————————— (T-Pair)
    Γ ⊢ {t1,t2} : T1 × T2 

    Γ ⊢ t1 : T11 × T12
    —————————————————— (T-Proj1)
    Γ ⊢ t1.1 : T11

    Γ ⊢ t1 : T11 × T12
    —————————————————— (T-Proj2)
    Γ ⊢ t1.2 : T12

## 図11-6.組

  →{}   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …       項：
      {ti i∈1..n} 組
      t.i          射影

    v ::= …       値：
      {vi i∈1..n} 組の値

    T ::= …       型：
      {Ti i∈1..n} 組の型

    新しい評価規則 t ==> t'

    {vi i∈1..n}.j ==> vj               (E-ProjTuple)

    t1 ==> t1'
    —————————————————— (E-Proj)
    t1.i ==> t1'.i

    tj ==> tj'
    —————————————————— (E-Tuple)
    {vi i∈1..j-1, tj, tk k∈j+1..n}
    ==> {vi i∈1..j-1, tj', tk k∈j+1..n}

    新しい型付け規則 Γ ⊢ t : T

    各iに対して Γ ⊢ ti : Ti
    —————————————————— (T-Tuple)
    Γ ⊢ {ti i∈1..n} : {Ti i∈1..n} 

    Γ ⊢ t1 : {Ti i∈1..n} 
    —————————————————— (T-Proj)
    Γ ⊢ t1.j : Tj

## 図11-7.レコード

  →{}   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …          項：
      {li=ti i∈1..n} レコード
      t.l             射影

    v ::= …      値：
      {li=vi i∈1..n} レコードの値

    T ::= …      型：
      {li:Ti i∈1..n} レコードの型

    新しい評価規則 t ==> t’

    {li=vi i∈1..n}.lj ==> vj            (E-ProjRcd)

    t1 ==> t1'
    —————————————————— (E-Proj)
    t1.l ==> t1'.l

    tj ==> tj'
    —————————————————— (E-Rcd)
    {li=vi i∈1..j-1, lj=tj, lk=tk k∈j+1..n}
    ==> {li=vi i∈1..j-1, lj=tj', lk=tk k∈j+1..n}


    新しい型付け規則 Γ ⊢ t : T

    各iに対して Γ ⊢ ti : Ti
    —————————————————— (T-Rcd)
    Γ ⊢ {li=ti i∈1..n} : {li:Ti i∈1..n} 

    Γ ⊢ t1 : {li:Ti i∈1..n} 
    —————————————————— (T-Proj)
    Γ ⊢ t1.lj : Tj

## 図11-8.(型無し)レコードパターン

  →{} let p(型無し)  図11-7と図11-4の拡張

    新しい構文形式

    p ::= x           変数パターン：

    t ::= …          項：
      let p=t in t    パターン束縛


    パターンマッチの規則

    match(x, v) = [x->v]                 (M-Var)

    各iに対して match(pi,vi) = σi
    —————————————————— (M-Rcd)
    match({li=pi i∈1..n} : {li=vi i∈1..n})
        = σ1 ∘ … ∘ σn

    新しい評価規則 t ==> t’

    let p=v1 in t2 ==> match(p, v1) t2   (E-LetV)

    t1 ==> t1'
    —————————————————— (E-Let)
    let p=t1 in t2 ==> let p=t1’ in t2

## 図11-9.和

  →+   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …                        項：
      inl t                         タグ付け（左）
      inr t                         タグ付け（右）
      case t of inl x=>t | inr x=>t 場合分け

    v ::= …                        値：
      inl v                         タグ付けの値（左）
      inr v                         タグ付けの値（右）

    T ::= …                        型：
      T+T                           和型

    新しい評価規則 t ==> t’

    case (inl v0)
    of inl x1 => t1 | inr x2 => t2
        ==> [x1 -> v0] t1             (E-CaseInl)

    case (inr v0)
    of inl x1 => t1 | inr x2 => t2
        ==> [x2 -> v0] t2             (E-CaseInr)

    t0 ==> t0'
    —————————————————— (E-Case)
    case t0 of inl x1=>t1 | inr x2=>t2
    ==> case t0’ of inl x1=>t1 | inr x2=>t2

    t1 ==> t1'
    —————————————————— (E-Inl)
    inl t1 ==> inl t1’

    t1 ==> t1'
    —————————————————— (E-Inr)
    inr t1 ==> inr t1’


    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 : T1
    —————————————————— (T-Inl)
    Γ ⊢ inl t1 : T1 + T2

    Γ ⊢ t1 : T2
    —————————————————— (T-Inr)
    Γ ⊢ inr t1 : T1 + T2

    Γ ⊢ t0 : T1 + T2
    Γ,x1:T1 ⊢ t1:T    Γ,x2:T2 ⊢ t2:T    
    ————————————————————— (T-Case)
    Γ ⊢ case t0 of inl x1=>t1 | inr x2=>t2:T

## 図11-10.和（一意型付け）

  →+   λ→(図9-1)の拡張

    新しい構文形式

    t ::= …                        項：
      inr v as T                    タグ付けの値（右）

    新しい評価規則 t ==> t’

    case (inl v0 as T0)
    of inl x1 => t1 | inr x2 => t2
        ==> [x1 -> v0] t1             (E-CaseInl)

    case (inr v0 as T0)
    of inl x1 => t1 | inr x2 => t2
        ==> [x2 -> v0] t2             (E-CaseInr)

    t1 ==> t1'
    —————————————————— (E-Inl)
    inl t1 as T2 ==> inl t1’ as T2

    t1 ==> t1'
    —————————————————— (E-Inr)
    inr t1 as T2 ==> inr t1’ as T2

    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 : T1
    —————————————————— (T-Inl)
    Γ ⊢ inl t1 as T1 + T2 : T1 + T2

    Γ ⊢ t1 : T2
    —————————————————— (T-Inr)
    Γ ⊢ inr t1 as T1 + T2 : T1 + T2

## 図11-11.バリアント

  →<>   λ→(図9-1)の拡張

    新しい構文形式

    t::= …                            項：
      <li:Ti i∈1..n>                  バリアント型

    新しい評価規則 t ==> t’

    case(<lj=vj as T) of <li=xi>=>Ti i∈1..n
        ==> [xj -> vj]tj         (E-CaseVariant)

    t0 ==> t0’
    ——————————————————— (E-Case)
    case t0 of <li=xi> => ti i ∈1..n
    ==> case t0’ of <li=xi> => ti i∈1..n

    ti ==> ti’
    ——————————————————(E-Variant)
    <li=ti> as T ==> <li=ti’> as T

    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ tj:Tj
    —————————————————— (T-Variant)
    Γ ⊢ <lj=tj> as <li:Ti i∈1..n> : <li:Ti i∈1..n>

    Γ ⊢ t0:<li:Ti i∈1..n>
    各iに対してΓ,xi:Ti ⊢ ti : T
    —————————————————— (T-Case)
    Γ ⊢ case t0 of <li:xi> => ti i∈1..n : T

## 図11-12.一般的再帰

  →fix   λ→(図9-1)の拡張

    新しい構文形式

    t::= …     項:
      fix t     tの不動点

    新しい評価規則 t ==> t’

    fix(λx:T1 . t2)
    ==> [x -> (fix (λx:T1 . t2))] t2 (E-FixBeta)


    t1 ==> t1’
    ————————(E-Fix)
    fix t1 ==> fix t1’

    新しい型付け規則 Γ ⊢ t : T

    Γ ⊢ t1 :T1 -> T1
    —————————— (T-Fix)
    Γ ⊢ fix t1 :T1

    新しい派生形式

    letrec x:T1 = t1 in t2
    def= let x = fix(λx:T1.t1) in t2

## 図11-13.リスト

  →B List   λ→(図9-1)のブール値(図8-1)を用いた拡張

    新しい構文形式
    t::=…項:
      nil[T] 空のリスト
      cons[T] t t リスト構築子(constructor)
      isnil[T] t リストが空かどうかの検査
      head[T] t リスト先頭の要素(head)
      tail[T] t リストの残りの部分(tail)
    v::= … 値:
      nil[T] 空のリスト
      cons[T] v v リスト構築子
    T::= … 型:
      List T リストの型


    新しい型付け規則
    Γ ⊢ nil[T1] : List T1 (T-Nil)

    Γ ⊢ t1 : T1    Γ ⊢ t2 : List T1
    ——————————————————(T-Cons)
    Γ ⊢ cons[T1]t1 t2 : List T1

    Γ ⊢ t1:T11
    ——————————————————(T-IsNil)
    Γ ⊢ isnil[T11]t1 : Bool

    Γ ⊢ t1 : List T11
    ———————————————(T-Head)
    Γ ⊢ t1 : head[T11]t1 : T11

    Γ ⊢ t1 : List T11
    ———————————————(T-Tail)
    Γ ⊢ t1 : tail[T11]t1 : List T11


    新しい評価規則

    t1 ==> t1’
    ——————————————— (E-Cons1)
    cons[T] t1 t2 ==> cons[T] t1’ t2

    t2 ==> t2’
    ——————————————— (E-Cons2)
    cons[T] v1 t2 ==> cons[T] v1 t2’

    isnil[S](nil[T])==>true               (E-IsNilNil)

    isnil[S](cons[T] v1 v2) ==> false (E-IsNilCons)

    t1 ==> t1’
    ——————————————— (E-IsNil)
    isnil[T] t1 ==> isnil[T] t1’

    head[S](cons[T] v1 v2) ==> v1 (E-HeadCons)

    t1 ==> t1’
    ——————————————— (E-Head)
    head[T]t1 ==> head[T]t1’

    tail[S](cons[T] v1 v2) ==> v2    (E-TailCons)

    t1==>t1’
    ——————————————— (E-Tail)
    tail[T]t1 ==> tail[T]t1’

