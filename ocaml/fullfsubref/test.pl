run([% lambda x:Bot.x
fn(x,bot,x),
% lambda x:Bot.x x
fn(x,bot,app(x,x)),
% lambda x:<a:Bool, b:Bool>.x
fn(x,variant([a:bool, b:bool]),x),
% lambda x:Top.x
fn(x,top,x),
% (lambda x:Top.x) (lambda x:Top.x)
app(fn(x,top,x),fn(x,top,x)),
% (lambda x:Top -> Top.x) (lambda x:Top.x)
app(fn(x,arr(top,top),x),fn(x,top,x)),
% (lambda r:{x:Top -> Top}.r.x r.x) {x=lambda z:Top.z, y=lambda z:Top.z}
app(fn(r,record([x:arr(top,top)]),app(proj(r,x),proj(r,x))),record([x=fn(z,top,z), y=fn(z,top,z)])),
% "hello"
"hello",
% unit
unit,
% lambda x:A.x
fn(x,'A',x),
% let x = true in x
let(x,true,x),
% {x=true, y=false}
record([x=true, y=false]),
% {x=true, y=false}.x
proj(record([x=true, y=false]),x),
% {true, false}
record([1=true, 2=false]),
% {true, false}.1
proj(record([1=true, 2=false]),1),
% if true then {x=true, y=false, a=false} else {y=false, x={}, b=false}
if(true,record([x=true, y=false, a=false]),record([y=false, x=record([]), b=false])),
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
% if error then true else false
if(error,true,false),
% error true
app(error,true),
% (lambda x:Bool.x) error
app(fn(x,bool,x),error),
% lambda x:Nat.succ x
fn(x,nat,succ(x)),
% (lambda x:Nat.succ (succ x)) 1
app(fn(x,nat,succ(succ(x))),succ(zero)),
% type('T')=Nat -> Nat
type('T') = arr(nat,nat),
% lambda f:T.lambda x:Nat.f (f x)
fn(f,'T',fn(x,nat,app(f,app(f,x)))),
% type('CounterRep')={x:Ref Nat}
type('CounterRep') = record([x:ref(nat)]),
% type('SetCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit)]),
% setCounterClass = lambda r:CounterRep.lambda self:Unit -> SetCounter.lambda _:Unit.{get=lambda _:Unit.!r.x, set=lambda i:Nat.r.x := i, inc=lambda _:Unit.(self unit).set (succ ((self unit).get unit))} as SetCounter
setCounterClass = fn(r,'CounterRep',fn(self,arr(unit,'SetCounter'),fn('_',unit,as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(app(self,unit),set),succ(app(proj(app(self,unit),get),unit))))]),'SetCounter')))),
% newSetCounter = lambda _:Unit.let r = {x=ref 1} in fix (setCounterClass r) unit
newSetCounter = fn('_',unit,let(r,record([x=ref(succ(zero))]),app(fix(app(setCounterClass,r)),unit))),
% c = newSetCounter unit
c = app(newSetCounter,unit),
% c.get unit
app(proj(c,get),unit),
% type('InstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat}
type('InstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat)]),
% type('InstrCounterRep')={x:Ref Nat, a:Ref Nat}
type('InstrCounterRep') = record([x:ref(nat), a:ref(nat)]),
% instrCounterClass = lambda r:InstrCounterRep.lambda self:Unit -> InstrCounter.lambda _:Unit.let super = setCounterClass r self unit in {get=super.get, set=lambda i:Nat.(lambda _:Unit.super.set i) (r.a := succ (!r.a)), inc=super.inc, accesses=lambda _:Unit.!r.a} as InstrCounter
instrCounterClass = fn(r,'InstrCounterRep',fn(self,arr(unit,'InstrCounter'),fn('_',unit,let(super,app(app(app(setCounterClass,r),self),unit),as(record([get=proj(super,get), set=fn(i,nat,app(fn('_',unit,app(proj(super,set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(super,inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter'))))),
% newInstrCounter = lambda _:Unit.let r = {x=ref 1, a=ref 0} in fix (instrCounterClass r) unit
newInstrCounter = fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero)]),app(fix(app(instrCounterClass,r)),unit))),
% ic = newInstrCounter unit
ic = app(newInstrCounter,unit),
% ic.get unit
app(proj(ic,get),unit),
% ic.accesses unit
app(proj(ic,accesses),unit),
% ic.inc unit
app(proj(ic,inc),unit),
% ic.get unit
app(proj(ic,get),unit),
% ic.accesses unit
app(proj(ic,accesses),unit),
% instrCounterClass = lambda r:InstrCounterRep.lambda self:Unit -> InstrCounter.lambda _:Unit.let super = setCounterClass r self unit in {get=lambda _:Unit.(lambda _:Unit.super.get unit) (r.a := succ (!r.a)), set=lambda i:Nat.(lambda _:Unit.super.set i) (r.a := succ (!r.a)), inc=super.inc, accesses=lambda _:Unit.!r.a} as InstrCounter
instrCounterClass = fn(r,'InstrCounterRep',fn(self,arr(unit,'InstrCounter'),fn('_',unit,let(super,app(app(app(setCounterClass,r),self),unit),as(record([get=fn('_',unit,app(fn('_',unit,app(proj(super,get),unit)),assign(proj(r,a),succ(deref(proj(r,a)))))), set=fn(i,nat,app(fn('_',unit,app(proj(super,set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(super,inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter'))))),
% type('ResetInstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat, reset:Unit -> Unit}
type('ResetInstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat), reset:arr(unit,unit)]),
% resetInstrCounterClass = lambda r:InstrCounterRep.lambda self:Unit -> ResetInstrCounter.lambda _:Unit.let super = instrCounterClass r self unit in {get=super.get, set=super.set, inc=super.inc, accesses=super.accesses, reset=lambda _:Unit.r.x := 0} as ResetInstrCounter
resetInstrCounterClass = fn(r,'InstrCounterRep',fn(self,arr(unit,'ResetInstrCounter'),fn('_',unit,let(super,app(app(app(instrCounterClass,r),self),unit),as(record([get=proj(super,get), set=proj(super,set), inc=proj(super,inc), accesses=proj(super,accesses), reset=fn('_',unit,assign(proj(r,x),zero))]),'ResetInstrCounter'))))),
% type('BackupInstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat, backup:Unit -> Unit, reset:Unit -> Unit}
type('BackupInstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat), backup:arr(unit,unit), reset:arr(unit,unit)]),
% type('BackupInstrCounterRep')={x:Ref Nat, a:Ref Nat, b:Ref Nat}
type('BackupInstrCounterRep') = record([x:ref(nat), a:ref(nat), b:ref(nat)]),
% backupInstrCounterClass = lambda r:BackupInstrCounterRep.lambda self:Unit -> BackupInstrCounter.lambda _:Unit.let super = resetInstrCounterClass r self unit in {get=super.get, set=super.set, inc=super.inc, accesses=super.accesses, reset=lambda _:Unit.r.x := !r.b, backup=lambda _:Unit.r.b := !r.x} as BackupInstrCounter
backupInstrCounterClass = fn(r,'BackupInstrCounterRep',fn(self,arr(unit,'BackupInstrCounter'),fn('_',unit,let(super,app(app(app(resetInstrCounterClass,r),self),unit),as(record([get=proj(super,get), set=proj(super,set), inc=proj(super,inc), accesses=proj(super,accesses), reset=fn('_',unit,assign(proj(r,x),deref(proj(r,b)))), backup=fn('_',unit,assign(proj(r,b),deref(proj(r,x))))]),'BackupInstrCounter'))))),
% newBackupInstrCounter = lambda _:Unit.let r = {x=ref 1, a=ref 0, b=ref 0} in fix (backupInstrCounterClass r) unit
newBackupInstrCounter = fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero), b=ref(zero)]),app(fix(app(backupInstrCounterClass,r)),unit))),
% ic = newBackupInstrCounter unit
ic = app(newBackupInstrCounter,unit),
% (lambda _:Unit.ic.get unit) (ic.inc unit)
app(fn('_',unit,app(proj(ic,get),unit)),app(proj(ic,inc),unit)),
% (lambda _:Unit.ic.get unit) (ic.backup unit)
app(fn('_',unit,app(proj(ic,get),unit)),app(proj(ic,backup),unit)),
% (lambda _:Unit.ic.get unit) (ic.inc unit)
app(fn('_',unit,app(proj(ic,get),unit)),app(proj(ic,inc),unit)),
% (lambda _:Unit.ic.get unit) (ic.reset unit)
app(fn('_',unit,app(proj(ic,get),unit)),app(proj(ic,reset),unit)),
% ic.accesses unit
app(proj(ic,accesses),unit),


% type('Counter')={get:Unit -> Nat, inc:Unit -> Unit}
type('Counter') = record([get:arr(unit,nat), inc:arr(unit,unit)]),
% inc3 = lambda c:Counter.(lambda _:Unit.(lambda _:Unit.c.inc unit) (c.inc unit)) (c.inc unit)
inc3 = fn(c,'Counter',app(fn('_',unit,app(fn('_',unit,app(proj(c,inc),unit)),app(proj(c,inc),unit))),app(proj(c,inc),unit))),
% type('SetCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit)]),
% type('InstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat}
type('InstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat)]),
% type('CounterRep')={x:Ref Nat}
type('CounterRep') = record([x:ref(nat)]),
% type('InstrCounterRep')={x:Ref Nat, a:Ref Nat}
type('InstrCounterRep') = record([x:ref(nat), a:ref(nat)]),
% dummySetCounter = {get=lambda _:Unit.0, set=lambda i:Nat.unit, inc=lambda _:Unit.unit} as SetCounter
dummySetCounter = as(record([get=fn('_',unit,zero), set=fn(i,nat,unit), inc=fn('_',unit,unit)]),'SetCounter'),
% dummyInstrCounter = {get=lambda _:Unit.0, set=lambda i:Nat.unit, inc=lambda _:Unit.unit, accesses=lambda _:Unit.0} as InstrCounter
dummyInstrCounter = as(record([get=fn('_',unit,zero), set=fn(i,nat,unit), inc=fn('_',unit,unit), accesses=fn('_',unit,zero)]),'InstrCounter'),
% setCounterClass = lambda r:CounterRep.lambda self:Source SetCounter.{get=lambda _:Unit.!r.x, set=lambda i:Nat.r.x := i, inc=lambda _:Unit.(!self).set (succ ((!self).get unit))} as SetCounter
setCounterClass = fn(r,'CounterRep',fn(self,source('SetCounter'),as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(deref(self),set),succ(app(proj(deref(self),get),unit))))]),'SetCounter'))),
% newSetCounter = lambda _:Unit.let r = {x=ref 1} in let cAux = ref dummySetCounter in (lambda _:Unit.!cAux) (cAux := setCounterClass r cAux)
newSetCounter = fn('_',unit,let(r,record([x=ref(succ(zero))]),let(cAux,ref(dummySetCounter),app(fn('_',unit,deref(cAux)),assign(cAux,app(app(setCounterClass,r),cAux)))))),
% instrCounterClass = lambda r:InstrCounterRep.lambda self:Source InstrCounter.let super = setCounterClass r self in {get=super.get, set=lambda i:Nat.(lambda _:Unit.super.set i) (r.a := succ (!r.a)), inc=super.inc, accesses=lambda _:Unit.!r.a} as InstrCounter
instrCounterClass = fn(r,'InstrCounterRep',fn(self,source('InstrCounter'),let(super,app(app(setCounterClass,r),self),as(record([get=proj(super,get), set=fn(i,nat,app(fn('_',unit,app(proj(super,set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(super,inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter')))),
% newInstrCounter = lambda _:Unit.let r = {x=ref 1, a=ref 0} in let cAux = ref dummyInstrCounter in (lambda _:Unit.!cAux) (cAux := instrCounterClass r cAux)
newInstrCounter = fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero)]),let(cAux,ref(dummyInstrCounter),app(fn('_',unit,deref(cAux)),assign(cAux,app(app(instrCounterClass,r),cAux)))))),
% c = newInstrCounter unit
c = app(newInstrCounter,unit),
% (lambda _:Unit.c.get unit) (inc3 c)
app(fn('_',unit,app(proj(c,get),unit)),app(inc3,c)),
% (lambda _:Unit.c.get unit) (c.set 54)
app(fn('_',unit,app(proj(c,get),unit)),app(proj(c,set),succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
% c.accesses unit
app(proj(c,accesses),unit),
% try if error then true else true with false
try(if(error,true,true),false)
]).
