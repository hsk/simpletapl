/* Examples for testing */

lambda x:Top. x;
(lambda x:Top. x) (lambda x:Top. x);
(lambda x:Top->Top. x) (lambda x:Top. x);


lambda x:Bot. x;
lambda x:Bot. x x;

y:Bot->Bot;
x:Bot;
y x;
/* z; error */
