import Data.Map (insert,empty)
import Data.Foldable (foldlM)

------------------------   SYNTAX  ------------------------

type X = String
data M = MVar X
       | MAbs X M
       | MApp M M
       deriving (Eq, Show, Read)
data C = Eval M
       | Bind X X
       deriving (Eq, Show, Read)

------------------------   SUBSTITUTION  ------------------------

subst j m (MVar x) | j == x    = do return m
subst j m (MVar x) | otherwise = do return $ MVar x
subst j m (MAbs x m2)          = do m2' <- subst2 x j m m2; return $ MAbs x m2'
subst j m (MApp m1 m2)         = do m1' <- subst j m m1 ; m2' <- subst j m m2; return $ MApp m1' m2'

subst2 x j m s | x == j    = do return $ s
subst2 x j m s | otherwise = subst j m s

getb g x = lookup x g

------------------------   EVALUATION  ------------------------

v (MAbs _ _) = True
v _          = False

eval1 g (MApp (MAbs x m12) v2) | v v2 = do subst x v2 m12
eval1 g (MApp v1 m2)           | v v1 = do m2' <- eval1 g m2; return $ MApp v1 m2'
eval1 g (MApp m1 m2)                  = do m1' <- eval1 g m1; return $ MApp m1' m2
eval1 g m                             = fail $ "eval1 error:" ++ show m

eval g m = maybe m (eval g) $ eval1 g m

------------------------   MAIN  ------------------------

run1 g (Eval m) = do
  let m' = eval g m
  putStrLn $ show m'
  return g
run1 g (Bind x bind) = do
  putStrLn x
  return $ insert x bind g
  
run ls = foldlM run1 empty ls

------------------------   TEST  ------------------------

main = do
  run [
    --x/;
    Bind x "bName",
    --x;
    Eval(MVar(x)),
    --lambda x. x;
    Eval(MAbs x (MVar(x))),
    --(lambda x. x) (lambda x. x x); 
    Eval(MApp (MAbs x (MVar(x))) (MAbs x (MApp (MVar(x)) (MVar(x)) )) ),
    --(lambda z. (lambda y. y) z) (lambda x. x x); 
    Eval(MApp (MAbs z (MApp (MAbs y (MVar(y))) (MVar(z)))) (MAbs x (MApp(MVar(x)) (MVar(x)) )) ),
    --(lambda x. (lambda x. x) x) (lambda x. x x); 
    Eval(MApp (MAbs x (MApp (MAbs x (MVar(x))) (MVar(x)))) (MAbs x (MApp(MVar(x)) (MVar(x)) )) ),
    --(lambda x. (lambda x. x) x) (lambda z. z z); 
    Eval(MApp (MAbs x (MApp (MAbs x (MVar(x))) (MVar(x)))) (MAbs z (MApp(MVar(z)) (MVar(z)) )) )
    ]
  where
    x = "x"
    y = "y"
    z = "z"
