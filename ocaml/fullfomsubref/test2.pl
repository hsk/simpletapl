run([% type('CounterRep')={x:Ref Nat}
type('CounterRep') = record([x:ref(nat)]),
% type('SetCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit)]),
% type('SetCounterMethodTable')={get:Ref <none:Unit, some:Unit -> Nat>, set:Ref <none:Unit, some:Nat -> Unit>, inc:Ref <none:Unit, some:Unit -> Unit>}
type('SetCounterMethodTable') = record([get:ref(variant([none:unit, some:arr(unit,nat)])), set:ref(variant([none:unit, some:arr(nat,unit)])), inc:ref(variant([none:unit, some:arr(unit,unit)]))]),
% packGet = lambda f:Unit -> Nat.<some=f> as <none:Unit, some:Unit -> Nat>
packGet = fn(f,arr(unit,nat),tag(some,f,variant([none:unit, some:arr(unit,nat)]))),
% unpackGet = lambda mt:SetCounterMethodTable.case !mt.get of <none=x>==>error | <some=f>==>f
unpackGet = fn(mt,'SetCounterMethodTable',case(deref(proj(mt,get)),[none=(x,error),some=(f,f)]),
% packSet = lambda f:Nat -> Unit.<some=f> as <none:Unit, some:Nat -> Unit>
packSet = fn(f,arr(nat,unit),tag(some,f,variant([none:unit, some:arr(nat,unit)]))),
% unpackSet = lambda mt:SetCounterMethodTable.case !mt.set of <none=x>==>error | <some=f>==>f
unpackSet = fn(mt,'SetCounterMethodTable',case(deref(proj(mt,set)),[none=(x,error),some=(f,f)]),
% packInc = lambda f:Unit -> Unit.<some=f> as <none:Unit, some:Unit -> Unit>
packInc = fn(f,arr(unit,unit),tag(some,f,variant([none:unit, some:arr(unit,unit)]))),
% unpackInc = lambda mt:SetCounterMethodTable.case !mt.inc of <none=x>==>error | <some=f>==>f
unpackInc = fn(mt,'SetCounterMethodTable',case(deref(proj(mt,inc)),[none=(x,error),some=(f,f)]),
% setCounterClass = lambda r:CounterRep.lambda self:SetCounterMethodTable.(lambda _:Unit.(lambda _:Unit.self.inc := packInc (lambda _:Unit.unpackSet self (succ (unpackGet self unit)))) (self.set := packSet (lambda i:Nat.r.x := i))) (self.get := packGet (lambda _:Unit.!r.x))
setCounterClass = fn(r,'CounterRep',fn(self,'SetCounterMethodTable',app(fn('_',unit,app(fn('_',unit,assign(proj(self,inc),app(packInc,fn('_',unit,app(app(unpackSet,self),succ(app(app(unpackGet,self),unit))))))),assign(proj(self,set),app(packSet,fn(i,nat,assign(proj(r,x),i)))))),assign(proj(self,get),app(packGet,fn('_',unit,deref(proj(r,x)))))))),
% setCounterClass = lambda M<:SetCounter.lambda R<:CounterRep.lambda self:Ref (R -> M).lambda r:R.{get=lambda _:Unit.!r.x, set=lambda i:Nat.r.x := i, inc=lambda _:Unit.(!self r).set (succ ((!self r).get unit))} as SetCounter
setCounterClass = tfn('M','SetCounter',tfn('R','CounterRep',fn(self,ref(arr('R','M')),fn(r,'R',as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(app(deref(self),r),set),succ(app(proj(app(deref(self),r),get),unit))))]),'SetCounter'))))),
% newSetCounter = lambda _:Unit.let m = ref (lambda r:CounterRep.error as SetCounter) in let m' = setCounterClass [SetCounter] [CounterRep] m in (lambda _:Unit.let r = {x=ref 1} in m' r) (m := m')
newSetCounter = fn('_',unit,let(m,ref(fn(r,'CounterRep',as(error,'SetCounter'))),let(m',app(tapp(tapp(setCounterClass,'SetCounter'),'CounterRep'),m),app(fn('_',unit,let(r,record([x=ref(succ(zero))]),app(m',r))),assign(m,m'))))),
% c = newSetCounter unit
c = app(newSetCounter,unit),
% c.get unit
app(proj(c,get),unit),
% c.set 3
app(proj(c,set),succ(succ(succ(zero)))),
% c.inc unit
app(proj(c,inc),unit),
% c.get unit
app(proj(c,get),unit),
% setCounterClass = lambda M<:SetCounter.lambda R<:CounterRep.lambda self:Ref (R -> M).lambda r:R.{get=lambda _:Unit.!r.x, set=lambda i:Nat.r.x := i, inc=lambda _:Unit.(!self r).set (succ ((!self r).get unit))} as SetCounter
setCounterClass = tfn('M','SetCounter',tfn('R','CounterRep',fn(self,ref(arr('R','M')),fn(r,'R',as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(app(deref(self),r),set),succ(app(proj(app(deref(self),r),get),unit))))]),'SetCounter'))))),
% type('InstrCounter')={get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit, accesses:Unit -> Nat}
type('InstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat)]),
% type('InstrCounterRep')={x:Ref Nat, a:Ref Nat}
type('InstrCounterRep') = record([x:ref(nat), a:ref(nat)]),
% instrCounterClass = lambda M<:InstrCounter.lambda R<:InstrCounterRep.lambda self:Ref (R -> M).lambda r:R.let super = setCounterClass [M] [R] self in {get=(super r).get, set=lambda i:Nat.(lambda _:Unit.(super r).set i) (r.a := succ (!r.a)), inc=(super r).inc, accesses=lambda _:Unit.!r.a} as InstrCounter
instrCounterClass = tfn('M','InstrCounter',tfn('R','InstrCounterRep',fn(self,ref(arr('R','M')),fn(r,'R',let(super,app(tapp(tapp(setCounterClass,'M'),'R'),self),as(record([get=proj(app(super,r),get), set=fn(i,nat,app(fn('_',unit,app(proj(app(super,r),set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(app(super,r),inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter')))))),
% newInstrCounter = lambda _:Unit.let m = ref (lambda r:InstrCounterRep.error as InstrCounter) in let m' = instrCounterClass [InstrCounter] [InstrCounterRep] m in (lambda _:Unit.let r = {x=ref 1, a=ref 0} in m' r) (m := m')
newInstrCounter = fn('_',unit,let(m,ref(fn(r,'InstrCounterRep',as(error,'InstrCounter'))),let(m',app(tapp(tapp(instrCounterClass,'InstrCounter'),'InstrCounterRep'),m),app(fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero)]),app(m',r))),assign(m,m'))))),
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
