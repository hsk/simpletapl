import Data.Foldable (foldlM)
------------------------   SYNTAX  ------------------------

data M = MTrue
       | MFalse
       | MIf M M M
       | MZero
       | MSucc M
       | MPred M
       | MIsZero M
       deriving (Eq, Read, Show)

data C = Eval M

n :: M -> Bool
n MZero      = True
n (MSucc n1) = n n1
n _          = False

v :: M -> Bool
v MTrue  = True
v MFalse = True
v v1     = n v1

------------------------   EVALUATION  ------------------------

eval1 :: M -> Maybe M
eval1 (MIf MTrue  m2 m3)          = do                   return $ m2
eval1 (MIf MFalse m2 m3)          = do                   return $ m3
eval1 (MIf m1 m2 m3)              = do m1' <- eval1 m1 ; return $ MIf m1' m2 m3
eval1 (MSucc m1)                  = do m1' <- eval1 m1 ; return $ MSucc m1' 
eval1 (MPred MZero)               = do                   return $ MZero
eval1 (MPred (MSucc n1))   | n n1 = do                   return $ n1
eval1 (MPred m1)                  = do m1' <- eval1 m1 ; return $ MPred m1' 
eval1 (MIsZero MZero)             = do                   return $ MTrue
eval1 (MIsZero (MSucc n1)) | n n1 = do                   return $ MFalse
eval1 (MIsZero m1)                = do m1' <- eval1 m1 ; return $ MIsZero m1'
eval1 _                           = Nothing

eval :: M -> M
eval m = maybe m eval $ eval1 m

------------------------   MAIN  ------------------------

run1 :: b -> C -> IO b
run1 g (Eval m) = do
  let m' = eval m
  putStrLn $ show m'
  return g

run :: Foldable t => t C -> IO [t1]
run ls = foldlM run1 [] ls 

------------------------   TEST  ------------------------

main :: IO ()
main = do
  run [Eval(MTrue)]
  run [Eval(MIf MFalse MTrue MFalse)]
  run [Eval(MZero)]
  run [Eval(MSucc(MPred(MZero)))]
  run [Eval(MIsZero(MPred(MSucc(MSucc(MZero)))))]
  run [Eval(MIsZero(MPred(MPred(MSucc(MSucc(MZero))))))]
  run [Eval(MIsZero(MZero))]
  run [Eval(MIf MZero (MSucc(MPred(MZero))) MZero)]
  run [Eval(MIf MZero (MSucc(MSucc(MZero))) MZero)]
  run [Eval(MIf MZero (MSucc(MPred(MSucc(MZero)))) MZero)]
  return ()
