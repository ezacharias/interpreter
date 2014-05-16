-- Let's work on this incrementally.
--   1. Do nothing but rename.
--   *. Count the size.
--   2. Attempt to drop unused instructions.
--   3. Use values.
--   4. Attempt to inline the continuation for case.
--   5. Attempt to inline functions.

module Compiler.Linear.Shrinker where

-- import Control.Applicative ((<|>))

import Compiler.Linear

shrink :: Program -> Program
shrink p = run p $ do
  xs <- mapM shrinkFun (programFuns p)
  return $ p {programFuns = xs}

shrinkFun :: (Ident, Fun) -> M (Ident, Fun)
shrinkFun (d1, Fun d2 ty1 ty2 t1) = do
  d1' <- renameFun d1
  d2' <- gen
  ty1' <- shrinkType ty1
  ty2' <- shrinkType ty2
  t1' <- bind d2 d2' $ do
    shrinkTerm t1
  return $ (d1', Fun d2' ty1' ty2' t1')

shrinkTerm :: Term -> M Term
shrinkTerm (ApplyTerm d1 d2 d3 t1) = do
  d1' <- gen
  d2' <- rename d2
  d3' <- rename d3
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ ApplyTerm d1' d2' d3' t1'
shrinkTerm (CallTerm d1 d2 d3s t1) = do
  d1' <- gen
  d2' <- renameFun d2
  d3s' <- mapM rename d3s
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ CallTerm d1' d2' d3s' t1'
shrinkTerm (CaseTerm d1 d2 c1s t1) = do
  d1' <- gen
  d2' <- rename d2
  c1s' <- mapM shrinkRule c1s
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ CaseTerm d1' d2' c1s' t1'
shrinkTerm (CatchTerm d1 d2 ty1 t1 t2) = do
  d1' <- gen
  d2' <- renameTag d2
  ty1' <- shrinkType ty1
  t1' <- shrinkTerm t1
  t2' <- bind d1 d1' $ do
    shrinkTerm t2
  return $ CatchTerm d1' d2' ty1'  t1' t2'
shrinkTerm (ConcatenateTerm d1 d2 d3 t1) = do
  d1' <- gen
  d2' <- rename d2
  d3' <- rename d3
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ ConcatenateTerm d1' d2' d3' t1'
shrinkTerm (ConstructorTerm d1 d2 i1 d3s t1) = do
  d1' <- gen
  d2' <- rename d2
  d3s' <- mapM rename d3s
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ ConstructorTerm d1' d2' i1 d3s' t1'
shrinkTerm (LambdaTerm d1 d2 ty1 t1 t2) = do
  d1' <- gen
  d2' <- gen
  ty1' <- shrinkType ty1
  t1' <- bind d2 d2' $ do
    shrinkTerm t1
  t2' <- bind d1 d1' $ do
    shrinkTerm t2
  return $ (LambdaTerm d1' d2' ty1' t1' t2')
shrinkTerm (ReturnTerm d1) = do
  d1' <- rename d1
  return $ ReturnTerm d1'
shrinkTerm (StringTerm d1 x1 t1) = do
  d1' <- gen
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ StringTerm d1' x1 t1'
shrinkTerm (ThrowTerm d1 d2 d3 t1) = do
  d1' <- gen
  d2' <- renameTag d2
  d3' <- rename d3
  t1' <- shrinkTerm t1
  return $ ThrowTerm d1' d2' d3' t1'
shrinkTerm (TupleTerm d1 d2s t1) = do -- Ident [Ident] Term
  d1' <- gen
  d2s' <- mapM rename d2s
  t1' <- bind d1 d1' $ do
    shrinkTerm t1
  return $ TupleTerm d1' d2s' t1'
shrinkTerm (UnreachableTerm ty1) = do
  ty1' <- shrinkType ty1
  return $ UnreachableTerm ty1'
shrinkTerm (UntupleTerm d1s d2 t1) = do
  d1s' <- mapM (const gen) d1s
  d2' <- rename d2
  t1' <- binds d1s' d1s $ do
    shrinkTerm t1
  return $ UntupleTerm d1s' d2' t1'

shrinkRule :: ([Ident], Term) -> M ([Ident], Term)
shrinkRule (d1s, t1) = do
  d1s' <- mapM (const gen) d1s
  t1' <- binds d1s d1s' $ do
    shrinkTerm t1
  return (d1s', t1')

shrinkType :: Type -> M Type
shrinkType ty1 = return $ ty1

newtype M a = M { runM :: [(Ident, Ident)] -> (a -> Int -> Program) -> Int -> Program }

instance Monad M where
  return x = M $ \ _ k -> k x
  m >>= f = M $ \ r k i -> runM m r (\ x i -> runM (f x) r k i) i

run :: Program -> M Program -> Program
run p m = undefined

bind :: Ident -> Ident -> M a -> M a
bind d1 d2 m = M $ \ r k i -> runM m ((d1,d2):r) k i

binds :: [Ident] -> [Ident] -> M a -> M a
binds [] [] m = m
binds (d1:d1s) (d2:d2s) m = bind d1 d2 $ binds d1s d2s m
binds _ _ _ = error "binds"

gen :: M Ident
gen = M $ \ _ k i -> k i (i + 1)

getEnv :: M [(Ident, Ident)]
getEnv = M $ \ r k i -> k r i

rename :: Ident -> M Ident
rename d = do
  r <- getEnv
  maybe (error "rename") return (lookup d r)

renameFun :: Ident -> M Ident
renameFun d1 = return d1

renameTag :: Ident -> M Ident
renameTag d1 = return d1
