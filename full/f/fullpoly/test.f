/* Examples for testing */

 "hello";

unit;

lambda x:A. x;

let x=true in x;

timesfloat 2.0 3.14159;
lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);


lambda X. lambda x:X. x; 
(lambda X. lambda x:X. x) [All X.X->X]; 

{*Nat, lambda x:Nat. succ x} as {Some X, X->Nat};

{*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};


{x=true, y=false}; 
{x=true, y=false}.x;
{true, false}; 
{true, false}.1; 


{*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};

let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}}
in (ops.f ops.c);
