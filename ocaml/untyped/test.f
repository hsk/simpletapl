/* Examples for testing */

x/;
x;

lambda x. x;
(lambda x. x) (lambda x. x x); 

(lambda z. (lambda y. y) z) (lambda x. x x); 
(lambda x. (lambda x. x) x) (lambda x. x x); 
(lambda x. (lambda x. x) x) (lambda z. z z); 
