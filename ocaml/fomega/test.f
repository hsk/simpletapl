/* Examples for testing */

lambda X. lambda x:X. x; 
(lambda X. lambda x:X. x) [All X.X->X]; 

T :: *;
k : T;
TT :: * => *;
kk : TT;

x : (lambda X::*=>*.T) T;
