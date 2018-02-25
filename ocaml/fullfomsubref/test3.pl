run([% type('CounterRep')={x:Ref Nat}
type('CounterRep') = record([x:ref(nat)]),
% type('SetCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit)]),
% setCounterClass = lambda R<:CounterRep.lambda self:R -> SetCounter.lambda r:R.{get=lambda _:Unit.!r.x, set=lambda i:Nat.r.x := i, inc=lambda _:Unit.(self r).set (succ ((self r).get unit))} as SetCounter
setCounterClass = tfn('R','CounterRep',fn(self,arr('R','SetCounter'),fn(r,'R',as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(app(self,r),set),succ(app(proj(app(self,r),get),unit))))]),'SetCounter')))),
% newSetCounter = lambda _:Unit.let r = {x=ref 1} in fix (setCounterClass [CounterRep]) r
newSetCounter = fn('_',unit,let(r,record([x=ref(succ(zero))]),app(fix(tapp(setCounterClass,'CounterRep')),r))),
% type('InstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat}
type('InstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat)]),
% type('InstrCounterRep')={x:Ref Nat, a:Ref Nat}
type('InstrCounterRep') = record([x:ref(nat), a:ref(nat)]),
% instrCounterClass = lambda R<:InstrCounterRep.lambda self:R -> InstrCounter.let super = setCounterClass [R] self in lambda r:R.{get=(super r).get, set=lambda i:Nat.(lambda _:Unit.(super r).set i) (r.a := succ (!r.a)), inc=(super r).inc, accesses=lambda _:Unit.!r.a} as InstrCounter
instrCounterClass = tfn('R','InstrCounterRep',fn(self,arr('R','InstrCounter'),let(super,app(tapp(setCounterClass,'R'),self),fn(r,'R',as(record([get=proj(app(super,r),get), set=fn(i,nat,app(fn('_',unit,app(proj(app(super,r),set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(app(super,r),inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter'))))),
% newInstrCounter = lambda _:Unit.let r = {x=ref 1, a=ref 0} in fix (instrCounterClass [InstrCounterRep]) r
newInstrCounter = fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero)]),app(fix(tapp(instrCounterClass,'InstrCounterRep')),r))),
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
app(proj(ic,accesses),unit)
]).
