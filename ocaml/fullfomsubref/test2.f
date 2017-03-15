CounterRep = {x: Ref Nat};
SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 


SetCounterMethodTable =  
{get: Ref <none:Unit, some:Unit->Nat>, 
set: Ref <none:Unit, some:Nat->Unit>, 
inc: Ref <none:Unit, some:Unit->Unit>}; 

packGet = 
lambda f:Unit->Nat. 
<some = f> as <none:Unit, some:Unit->Nat>;

unpackGet = 
lambda mt:SetCounterMethodTable.
case !(mt.get) of
<none=x> ==> error
| <some=f> ==> f;

packSet = 
lambda f:Nat->Unit. 
<some = f> as <none:Unit, some:Nat->Unit>;

unpackSet = 
lambda mt:SetCounterMethodTable.
case !(mt.set) of
<none=x> ==> error
| <some=f> ==> f;

packInc = 
lambda f:Unit->Unit. 
<some = f> as <none:Unit, some:Unit->Unit>;

unpackInc = 
lambda mt:SetCounterMethodTable.
case !(mt.inc) of
<none=x> ==> error
| <some=f> ==> f;

setCounterClass =
lambda r:CounterRep.
lambda self: SetCounterMethodTable.
(self.get := packGet (lambda _:Unit. !(r.x));
self.set := packSet (lambda i:Nat.  r.x:=i);
self.inc := packInc (lambda _:Unit. unpackSet self (succ (unpackGet self unit))));


/* This diverges... */
/*
setCounterClass =
lambda R<:CounterRep.
lambda self: R->SetCounter.
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (self r).set (succ((self r).get unit))} 
    as SetCounter;

newSetCounter = 
lambda _:Unit.
let r = {x=ref 1} in
fix (setCounterClass [CounterRep]) r;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda R<:InstrCounterRep.
lambda self: R->InstrCounter.
let super = setCounterClass [R] self in
lambda r:R.
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)} as InstrCounter;


newInstrCounter = 
lambda _:Unit.
let r = {x=ref 1, a=ref 0} in
fix (instrCounterClass [InstrCounterRep]) r;

SET traceeval;

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
*/

/* This is cool... */

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;


newSetCounter = 
lambda _:Unit.
let m = ref (lambda r:CounterRep. error as SetCounter) in
let m' = setCounterClass [SetCounter] [CounterRep] m in
(m := m';
let r = {x=ref 1} in
m' r);

c = newSetCounter unit;

c.get unit;

c.set 3;

c.inc unit;

c.get unit;

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda M<:InstrCounter.
lambda R<:InstrCounterRep.
lambda self: Ref(R->M).
lambda r: R.
let super = setCounterClass [M] [R] self in
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)}     as InstrCounter;

newInstrCounter = 
lambda _:Unit.
let m = ref (lambda r:InstrCounterRep. error as InstrCounter) in
let m' = instrCounterClass [InstrCounter] [InstrCounterRep] m in
(m := m';
let r = {x=ref 1, a=ref 0} in
m' r);

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
