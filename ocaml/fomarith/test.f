Pair X Y = All R.(X->Y->R)->R;
pair = \X.\Y.\x:X.\y:Y.\R.\p:X->Y->R.p x y;
fst = \X.\Y.\p:Pair X Y.p[X](\x:X.\y:Y.x);
snd = \X.\Y.\p:Pair X Y.p[Y](\x:X.\y:Y.y);

pr = pair[Nat][Bool] 0 false;
fst[Nat][Bool]pr;
snd[Nat][Bool]pr;

List X = All R. (X->R->R) -> R -> R; 

diverge =
\X.
  \_:Unit.
  fix (\x:X. x);

nil = \X.
      (\R. \c:X->R->R. \n:R. n)
      as List X; 

cons = 
\X.
  \hd:X. \tl: List X.
     (\R. \c:X->R->R. \n:R. c hd (tl [R] c n))
     as List X; 

isnil =  
\X. 
  \l: List X. 
    l [Bool] (\hd:X. \tl:Bool. false) true; 

head = 
\X. 
  \l: List X. 
    (l [Unit->X] (\hd:X. \tl:Unit->X. \_:Unit. hd) (diverge [X]))
    unit; 

tail =  
\X.  
  \l: List X. 
    (fst [List X] [List X] ( 
      l [Pair (List X) (List X)]
        (\hd: X. \tl: Pair (List X) (List X). 
          pair [List X] [List X] 
            (snd [List X] [List X] tl)  
            (cons [X] hd (snd [List X] [List X] tl))) 
        (pair [List X] [List X] (nil [X]) (nil [X]))))
    as List X; 
