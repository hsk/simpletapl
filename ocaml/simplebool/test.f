/* Examples for testing */

lambda x:Bool. x;
lambda x:Bool.lambda x:Bool. x;

 (lambda x:Bool->Bool. if x false then true else false) 
   (lambda x:Bool. if x then false else true); 
a:Bool;
a;
(lambda x:Bool. x) a;
(lambda x:Bool. (lambda x:Bool. x) x) a;
(lambda x:Bool. (lambda x:Bool. x) x) true;
