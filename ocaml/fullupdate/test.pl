run([% lambda x:Top.x
fn(x,top,x),
% (lambda x:Top.x) (lambda x:Top.x)
app(fn(x,top,x),fn(x,top,x)),
% (lambda x:Top -> Top.x) (lambda x:Top.x)
app(fn(x,arr(top,top),x),fn(x,top,x)),
% (lambda r:{x:Top -> Top}.r.x r.x) {x=lambda z:Top.z, y=lambda z:Top.z}
app(fn(r,record([x:(covariant,arr(top,top))]),app(proj(r,x),proj(r,x))),record([x=(covariant,fn(z,top,z)), y=(covariant,fn(z,top,z))])),
% "hello"
"hello",
% unit
unit,
% lambda x:A.x
fn(x,'A',x),
% let x = true in x
let(x,true,x),
% {x=true, y=false}
record([x=(covariant,true), y=(covariant,false)]),
% {x=true, y=false}.x
proj(record([x=(covariant,true), y=(covariant,false)]),x),
% {true, false}
record([1=(covariant,true), 2=(covariant,false)]),
% {true, false}.1
proj(record([1=(covariant,true), 2=(covariant,false)]),1),
% if true then {x=true, y=false, a=false} else {y=false, x={}, b=false}
if(true,record([x=(covariant,true), y=(covariant,false), a=(covariant,false)]),record([y=(covariant,false), x=(covariant,record([])), b=(covariant,false)])),
% timesfloat 2. 3.14159
timesfloat(2.,3.14159),
% lambda X.lambda x:X.x
tfn('X',top,fn(x,'X',x)),
% (lambda X.lambda x:X.x) [All X.X -> X]
tapp(tfn('X',top,fn(x,'X',x)),all('X',top,arr('X','X'))),
% lambda X<:Top -> Top.lambda x:X.x x
tfn('X',arr(top,top),fn(x,'X',app(x,x))),
% lambda x:Bool.x
fn(x,bool,x),
% (lambda x:Bool -> Bool.if x false then true else false) (lambda x:Bool.if x then false else true)
app(fn(x,arr(bool,bool),if(app(x,false),true,false)),fn(x,bool,if(x,false,true))),
% lambda x:Nat.succ x
fn(x,nat,succ(x)),
% (lambda x:Nat.succ (succ x)) 1
app(fn(x,nat,succ(succ(x))),succ(zero)),
% type('T')=Nat -> Nat
type('T') = arr(nat,nat),
% lambda f:T.lambda x:Nat.f (f x)
fn(f,'T',fn(x,nat,app(f,app(f,x)))),
% {*All Y.Y,lambda x:All Y.Y.x} as {Some X,X -> X}
pack(all('Y',top,'Y'),fn(x,all('Y',top,'Y'),x),some('X',top,arr('X','X'))),
% {*Nat,{c=0, f=lambda x:Nat.succ x}} as {Some X,{c:X, f:X -> Nat}}
pack(nat,record([c=(covariant,zero), f=(covariant,fn(x,nat,succ(x)))]),some('X',top,record([c:(covariant,'X'), f:(covariant,arr('X',nat))]))),
% let {X,ops}={*Nat,{c=0, f=lambda x:Nat.succ x}} as {Some X,{c:X, f:X -> Nat}} in ops.f ops.c
unpack('X',ops,pack(nat,record([c=(covariant,zero), f=(covariant,fn(x,nat,succ(x)))]),some('X',top,record([c:(covariant,'X'), f:(covariant,arr('X',nat))]))), app(proj(ops,f),proj(ops,c))),
% type('Pair')=lambda X.lambda Y.All R.(X -> Y -> R) -> R
type('Pair') = abs('X',*,abs('Y',*,all('R',top,arr(arr('X',arr('Y','R')),'R')))),
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X -> Y -> R.p x y
pair = tfn('X',top,tfn('Y',top,fn(x,'X',fn(y,'Y',tfn('R',top,fn(p,arr('X',arr('Y','R')),app(app(p,x),y))))))),
% f = lambda X.lambda Y.lambda f:Pair X Y.f
f = tfn('X',top,tfn('Y',top,fn(f,app(app('Pair','X'),'Y'),f))),
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x)
fst = tfn('X',top,tfn('Y',top,fn(p,app(app('Pair','X'),'Y'),app(tapp(p,'X'),fn(x,'X',fn(y,'Y',x)))))),
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y)
snd = tfn('X',top,tfn('Y',top,fn(p,app(app('Pair','X'),'Y'),app(tapp(p,'Y'),fn(x,'X',fn(y,'Y',y)))))),
% pr = pair [Nat] [Bool] 0 false
pr = app(app(tapp(tapp(pair,nat),bool),zero),false),
% fst [Nat] [Bool] pr
app(tapp(tapp(fst,nat),bool),pr),
% snd [Nat] [Bool] pr
app(tapp(tapp(snd,nat),bool),pr),
% type('List')=lambda X.All R.(X -> R -> R) -> R -> R
type('List') = abs('X',*,all('R',top,arr(arr('X',arr('R','R')),arr('R','R')))),
% diverge = lambda X.lambda _:Unit.(lambda x:X.x)
diverge = tfn('X',top,fn('_',unit,fix(fn(x,'X',x)))),
% nil = lambda X.(lambda R.lambda c:X -> R -> R.lambda n:R.n) as List X
nil = tfn('X',top,as(tfn('R',top,fn(c,arr('X',arr('R','R')),fn(n,'R',n))),app('List','X'))),
% cons = lambda X.lambda hd:X.lambda tl:List X.(lambda R.lambda c:X -> R -> R.lambda n:R.c hd (tl [R] c n)) as List X
cons = tfn('X',top,fn(hd,'X',fn(tl,app('List','X'),as(tfn('R',top,fn(c,arr('X',arr('R','R')),fn(n,'R',app(app(c,hd),app(app(tapp(tl,'R'),c),n))))),app('List','X'))))),
% isnil = lambda X.lambda l:List X.l [Bool] (lambda hd:X.lambda tl:Bool.false) true
isnil = tfn('X',top,fn(l,app('List','X'),app(app(tapp(l,bool),fn(hd,'X',fn(tl,bool,false))),true))),
% head = lambda X.lambda l:List X.l [Unit -> X] (lambda hd:X.lambda tl:Unit -> X.lambda _:Unit.hd) (diverge [X]) unit
head = tfn('X',top,fn(l,app('List','X'),app(app(app(tapp(l,arr(unit,'X')),fn(hd,'X',fn(tl,arr(unit,'X'),fn('_',unit,hd)))),tapp(diverge,'X')),unit))),
% tail = lambda X.lambda l:List X.(fst [List X] [List X] (l [Pair (List X) (List X)] (lambda hd:X.lambda tl:Pair (List X) (List X).pair [List X] [List X] (snd [List X] [List X] tl) (cons [X] hd (snd [List X] [List X] tl))) (pair [List X] [List X] (nil [X]) (nil [X])))) as List X
tail = tfn('X',top,fn(l,app('List','X'),as(app(tapp(tapp(fst,app('List','X')),app('List','X')),app(app(tapp(l,app(app('Pair',app('List','X')),app('List','X'))),fn(hd,'X',fn(tl,app(app('Pair',app('List','X')),app('List','X')),app(app(tapp(tapp(pair,app('List','X')),app('List','X')),app(tapp(tapp(snd,app('List','X')),app('List','X')),tl)),app(app(tapp(cons,'X'),hd),app(tapp(tapp(snd,app('List','X')),app('List','X')),tl)))))),app(app(tapp(tapp(pair,app('List','X')),app('List','X')),tapp(nil,'X')),tapp(nil,'X')))),app('List','X'))))
]).
