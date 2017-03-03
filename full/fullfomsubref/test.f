/* Examples for testing */

 lambda x:Bot. x;
 lambda x:Bot. x x; 

 
lambda x:<a:Bool,b:Bool>. x;


lambda x:Top. x;
 (lambda x:Top. x) (lambda x:Top. x);
(lambda x:Top->Top. x) (lambda x:Top. x);


(lambda r:{x:Top->Top}. r.x r.x) 
  {x=lambda z:Top.z, y=lambda z:Top.z}; 

"hello";

unit;

lambda x:A. x;

let x=true in x;

{x=true, y=false}; 
{x=true, y=false}.x;
{true, false}; 
{true, false}.1; 


if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

try if error then true else true with false;
try {error,true} with {unit,false};

timesfloat 2.0 3.14159;

lambda X. lambda x:X. x; 
(lambda X. lambda x:X. x) [Nat]; 

lambda X<:Top->Top. lambda x:X. x x; 


lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

if error then true else false;


error true;
(lambda x:Bool. x) error;





lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);




/* Alternative object encodings */

CounterRep = {x: Ref Nat};

SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 

setCounterClass =
lambda r:CounterRep.
lambda self: Unit->SetCounter.
lambda _:Unit.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (self unit).set (succ((self unit).get unit))} 
    as SetCounter;

newSetCounter = 
lambda _:Unit.
let r = {x=ref 1} in
fix (setCounterClass r) unit;

c = newSetCounter unit;
c.get unit;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda r:InstrCounterRep.
lambda self: Unit->InstrCounter.
lambda _:Unit.
let super = setCounterClass r self unit in
{get = super.get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
inc = super.inc,
accesses = lambda _:Unit. !(r.a)} as InstrCounter;

newInstrCounter = 
lambda _:Unit.
let r = {x=ref 1, a=ref 0} in
fix (instrCounterClass r) unit;

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;

/* ------------ */

instrCounterClass =
lambda r:InstrCounterRep.
lambda self: Unit->InstrCounter.
lambda _:Unit.
let super = setCounterClass r self unit in
{get = lambda _:Unit. (r.a:=succ(!(r.a)); super.get unit),
set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
inc = super.inc,
accesses = lambda _:Unit. !(r.a)} as InstrCounter;

ResetInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
inc:Unit->Unit, accesses:Unit->Nat,
reset:Unit->Unit};

resetInstrCounterClass =
lambda r:InstrCounterRep.
lambda self: Unit->ResetInstrCounter.
lambda _:Unit.
let super = instrCounterClass r self unit in
{get = super.get,
set = super.set,
inc = super.inc,
accesses = super.accesses,
reset = lambda _:Unit. r.x:=0} 
as ResetInstrCounter;

BackupInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
inc:Unit->Unit, accesses:Unit->Nat,
backup:Unit->Unit, reset:Unit->Unit};

BackupInstrCounterRep = {x: Ref Nat, a: Ref Nat, b: Ref Nat};

backupInstrCounterClass =
lambda r:BackupInstrCounterRep.
lambda self: Unit->BackupInstrCounter.
lambda _:Unit.
let super = resetInstrCounterClass r self unit in
{get = super.get,
set = super.set,
inc = super.inc,
accesses = super.accesses,
reset = lambda _:Unit. r.x:=!(r.b),
backup = lambda _:Unit. r.b:=!(r.x)} 
as BackupInstrCounter;

newBackupInstrCounter = 
lambda _:Unit.
let r = {x=ref 1, a=ref 0, b=ref 0} in
fix (backupInstrCounterClass r) unit;

ic = newBackupInstrCounter unit;

(ic.inc unit; ic.get unit);

(ic.backup unit; ic.get unit);

(ic.inc unit; ic.get unit);

(ic.reset unit; ic.get unit);

ic.accesses unit;




/*
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
*/

/* This diverges...

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

/* This is cool...

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
*/

/* James Reily's alternative: */

Counter = {get:Unit->Nat, inc:Unit->Unit};
inc3 = lambda c:Counter. (c.inc unit; c.inc unit; c.inc unit);

SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit};
InstrCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat};

CounterRep = {x: Ref Nat};
InstrCounterRep = {x: Ref Nat, a: Ref Nat};

dummySetCounter =
{get = lambda _:Unit. 0,
set = lambda i:Nat.  unit,
inc = lambda _:Unit. unit}
as SetCounter;
dummyInstrCounter =
{get = lambda _:Unit. 0,
set = lambda i:Nat.  unit,
inc = lambda _:Unit. unit,
accesses = lambda _:Unit. 0}
as InstrCounter;
setCounterClass =
lambda r:CounterRep.
lambda self: Source SetCounter.     
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat. r.x:=i,
inc = lambda _:Unit. (!self).set (succ ((!self).get unit))}
as SetCounter;
newSetCounter =
lambda _:Unit. let r = {x=ref 1} in
let cAux = ref dummySetCounter in
(cAux :=
(setCounterClass r cAux);
!cAux);

instrCounterClass =
lambda r:InstrCounterRep.
lambda self: Source InstrCounter.       /* NOT Ref */
let super = setCounterClass r self in
{get = super.get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
inc = super.inc,
accesses = lambda _:Unit. !(r.a)}
as InstrCounter;
newInstrCounter =
lambda _:Unit. let r = {x=ref 1, a=ref 0} in
let cAux = ref dummyInstrCounter in
(cAux :=
(instrCounterClass r cAux);
!cAux);

c = newInstrCounter unit;
(inc3 c; c.get unit);
(c.set(54); c.get unit);
(c.accesses unit);


