/* Examples for testing */

 let x=true in x;

lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

lambda x:A. x;


(lambda x:X. lambda y:X->X. y x);
(lambda x:X->X. x 0) (lambda y:Nat. y); 



(lambda x. x 0);
let f = lambda x. x in (f f) (f 0);
let g = lambda x. 1 in g (g g);

