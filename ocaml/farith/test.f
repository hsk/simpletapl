/* Examples for testing */

lambda x:A. x;

let x=true in x;

lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);


lambda X. lambda x:X. x; 
(lambda X. lambda x:X. x) [All X.X->X]; 
