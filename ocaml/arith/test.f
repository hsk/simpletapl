/* Examples for testing */

true;
if false then true else false; 

0; 
succ (pred 0);
iszero (pred (succ (succ 0))); 
iszero (pred (pred (succ (succ 0)))); 
iszero 0;

if 0 then succ(pred 0) else 0;
if 0 then succ(succ 0) else 0;
if 0 then succ(pred (succ 0)) else 0;
