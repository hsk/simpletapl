/* Examples for testing */

 lambda x:Bool. x;
 lambda x:Bool. x;
 (lambda x:Bool->Bool. if x false then true else false) 
   (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

lambda x:A. x;


(lambda x:X. lambda y:X->X. y x);
(lambda x:X->X. x 0) (lambda y:Nat. y); 

if true then false else true;
if true then 1 else 0;

(lambda x:Nat. x) 0;
