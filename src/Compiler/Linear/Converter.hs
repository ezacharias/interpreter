-- | Converts a program from Simple to Linear.
module Compiler.Linear.Converter where

import qualified Compiler.Simple as Simple
import qualified Compiler.Linear as Linear

convert :: Simple.Program -> Linear.Program
convert p = run p $ do
  xs1 <- mapM convertTag (Simple.programTags p)
  xs2 <- mapM convertType (Simple.programRess p)
  xs3 <- mapM convertSum (Simple.programSums p)
  xs4 <- mapM convertFun (Simple.programFuns p)
  d <- renameFun (Simple.programMain p)
  return $ Linear.Program
             { Linear.programTags = xs1
             , Linear.programRess = xs2
             , Linear.programSums = xs3
             , Linear.programFuns = xs4
             , Linear.programMain = d
             }

run :: Simple.Program -> M Linear.Program Linear.Program -> Linear.Program
run p m = runM m k1 k2
  where k1 x k2 = k2 x
        k2 x = x

convertTag :: (Simple.Ident, Simple.Tag) -> P (Linear.Ident, Linear.Tag)
convertTag = todo "convertTag"

convertSum :: (Simple.Ident, Simple.Sum) -> P (Linear.Ident, Linear.Sum)
convertSum = todo "convertSum"

convertFun :: (Simple.Ident, Simple.Fun) -> P (Linear.Ident, Linear.Fun)
convertFun (d1, Simple.Fun ty1 t1) = do
  d1' <- renameFun d1
  ty' <- convertType ty1
  t1' <- result $ convertTerm t1
  return (d1', Linear.Fun [] [] ty' t1')

convertTerm :: Simple.Term -> T Simple.Ident
convertTerm (Simple.ApplyTerm t1 t2) = do
  d1' <- convertTerm t1
  d2' <- convertTerm t2
  d3' <- gen
  continue d3' $ \ t3' -> do
    return $ Linear.ApplyTerm d3' d1' d2' t3'
convertTerm (Simple.BindTerm d1 t1 t2) = do
  d1' <- convertTerm t1
  bind d1 d1' $ do
    convertTerm t2
convertTerm (Simple.CaseTerm t1 c1s) = do
  d1' <- convertTerm t1
  c1s' <- mapM convertRule c1s
  d2' <- gen
  continue d2' $ \ t1' -> do
    return $ Linear.CaseTerm d2' d1' c1s' t1'
convertTerm (Simple.CatchTerm d1 _ ty1 t1) = do
  d1' <- renameTag d1
  ty1' <- convertType ty1
  t2' <- result $ convertTerm t1
  d2' <- gen
  continue d2' $ \ t3' -> do
    return $ Linear.CatchTerm d2' d1' ty1' t2' t3'
convertTerm (Simple.ConcatenateTerm t1 t2) = do
  d1' <- convertTerm t1
  d2' <- convertTerm t2
  d3' <- gen
  continue d3' $ \ t3' -> do
    return $ Linear.ConcatenateTerm d3' d1' d2' t3'
convertTerm (Simple.ConstructorTerm d1 i1 t1s) = do
  d1' <- renameSum d1
  d2s' <- convertTerms t1s
  d3' <- gen
  continue d3' $ \ t2' -> do
    return $ Linear.ConstructorTerm d3' d1' i1 d2s' t2'
convertTerm (Simple.FunTerm d1) = do
  d1' <- renameFun d1
  d2' <- gen
  continue d2' $ \ t1' -> do
    return $ Linear.CallTerm d2' d1' [] t1'
convertTerm (Simple.LambdaTerm d1 ty1 t1) = do
  d1' <- gen
  d2' <- gen
  ty1' <- undefined
  t1' <- result $ bind d1 d1' (convertTerm t1)
  continue d2' $ \ t2' -> do
    return $ Linear.LambdaTerm d2' d1' ty1' t1' t2'
convertTerm (Simple.StringTerm x) = do
  d1' <- gen
  continue d1' $ \ t1' -> do
    return $ Linear.StringTerm d1' x t1'
convertTerm (Simple.ThrowTerm d1 t1) = do
  d1' <- renameTag d1
  d2' <- convertTerm t1
  d3' <- gen
  continue d3' $ \ t2' -> do
    return $ Linear.ThrowTerm d3' d1' d2' t2'
convertTerm (Simple.TupleTerm t1s) = do
  d1s' <- convertTerms t1s
  d2' <- gen
  continue d2' $ \ t2' -> do
    return $ Linear.TupleTerm d2' d1s' t2'
convertTerm Simple.UnitTerm = do
  d1' <- gen
  continue d1' $ \ t1' -> do
    return $ Linear.TupleTerm d1' [] t1'
convertTerm (Simple.UnreachableTerm ty) = do
  ty' <- convertType ty
  escape $ Linear.UnreachableTerm ty'
convertTerm (Simple.UntupleTerm d1s t1 t2) = do
  d1s' <- mapM (const gen) d1s
  d2' <- convertTerm t1
  binds d1s d1s' $ do
    adjust (convertTerm t2) (Linear.UntupleTerm d1s' d2')
convertTerm (Simple.VariableTerm d1) = do
  rename d1

convertRule :: ([Simple.Ident], Simple.Term) -> T ([Linear.Ident], Linear.Term)
convertRule (d1s, t1) = do
  d1s' <- mapM (const gen) d1s
  t1' <- result $ binds d1s d1s' (convertTerm t1)
  return (d1s', t1')

convertType :: Simple.Type -> M a Linear.Type
convertType = undefined

convertTerms :: [Simple.Term] -> T [Linear.Ident]
convertTerms [] = do
  return []
convertTerms (t:ts) = do
  d <- convertTerm t
  ds <- convertTerms ts
  return $ d:ds

newtype M a b = N { runM :: (b -> (a -> Linear.Program) -> Linear.Program) -> (a -> Linear.Program) -> Linear.Program }

type P a = M Linear.Program a

type T a = M Linear.Term a

instance Monad (M a) where
  return x = N $ \ k1 k2 -> k1 x k2
  m >>= f = N $ \ k1 k2 -> runM m (\ x k2 -> runM (f x) k1 k2) k2

gen :: M a Linear.Ident
gen = undefined

renameTag :: Simple.Ident -> M a Linear.Ident
renameTag d = return d

renameFun :: Simple.Ident -> M a Linear.Ident
renameFun d = return d

renameSum :: Simple.Ident -> M a Linear.Ident
renameSum d = return d

rename :: Simple.Ident -> M a Linear.Ident
rename = undefined

bind :: Simple.Ident -> Linear.Ident -> M a b -> M a b
bind d1 d2 m = undefined

binds :: [Simple.Ident] -> [Linear.Ident] -> M a b -> M a b
binds [] [] m = m
binds (d1:d1s) (d2:d2s) m = bind d1 d2 $ binds d1s d2s m
binds _ _ _ = error "binds"

continue :: Linear.Ident -> (Linear.Term -> T Linear.Term) -> T Linear.Ident
continue d f = N $ \ k1 k2 -> k1 d (\ t -> runM (f t) (\ t k2 -> k2 t) k2)

adjust :: T Linear.Ident -> (Linear.Term -> Linear.Term) -> T Linear.Ident
adjust m f = N $ \ k1 k2 -> runM m k1 (\ t -> k2 (f t))

escape :: Linear.Term -> T Linear.Ident
escape t = N $ \ k1 k2 -> k2 t

result :: T Simple.Ident -> M a Linear.Term
result m = N $ \ k1 k2 -> runM m (\ d1 k2 -> k2 (Linear.ReturnTerm d1)) (\ t1 -> k1 t1 k2)

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Linear.Converter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Linear.Converter." ++ s
