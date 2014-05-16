module Compiler.Linear.Converter where

import qualified Compiler.Simple as Simple
import qualified Compiler.Linear as Linear

convert :: Simple.Program -> Linear.Program
convert = undefined

convertFun :: (Simple.Ident, Simple.Fun) -> M Simple.Fun
convertFun (d1, Simple.Fun ty1 t1) = do
  t1' <- result (convertTerm t1) $ \ d1 -> do
    return $ Linear.ReturnTerm d1
  undefined

gen :: M Linear.Ident
gen = undefined

convertTerm :: Simple.Term -> M Simple.Ident
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
  t2' <- result (convertTerm t1) (\ d -> return $ Linear.ReturnTerm d)
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
  t1' <- result (bind d1 d1' (convertTerm t1)) (\ d -> return $ Linear.ReturnTerm d)
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

convertRule :: ([Simple.Ident], Simple.Term) -> M ([Linear.Ident], Linear.Term)
convertRule (d1s, t1) = do
  d1s' <- mapM (const gen) d1s
  t1' <- result (binds d1s d1s' $ convertTerm t1) (\ d -> return $ Linear.ReturnTerm d)
  return (d1s', t1')

convertType :: Simple.Type -> M Linear.Type
convertType = undefined

convertTerms :: [Simple.Term] -> M [Linear.Ident]
convertTerms [] = do
  return []
convertTerms (t:ts) = do
  d <- convertTerm t
  ds <- convertTerms ts
  return $ d:ds

rename :: Simple.Ident -> M Linear.Ident
rename = undefined

renameTag :: Simple.Ident -> M Linear.Ident
renameTag = undefined

renameFun :: Simple.Ident -> M Linear.Ident
renameFun = undefined

renameSum :: Simple.Ident -> M Linear.Ident
renameSum = undefined

bind :: Simple.Ident -> Linear.Ident -> M Simple.Ident -> M Linear.Ident
bind d1 d2 m = undefined

binds :: [Simple.Ident] -> [Linear.Ident] -> M Simple.Ident -> M Linear.Ident
binds = undefined

continue :: Linear.Ident -> (Linear.Term -> M Linear.Term) -> M Linear.Ident
continue d f = N $ \ k1 k2 -> k1 d (\ t -> runN (f t) (\ t k2 -> k2 t) k2)

adjust :: M Linear.Ident -> (Linear.Term -> Linear.Term) -> M Linear.Ident
adjust m f = N $ \ k1 k2 -> runN m k1 (\ t -> k2 (f t))

escape :: Linear.Term -> M Linear.Ident
escape t = N $ \ k1 k2 -> k2 t

result :: M Simple.Ident -> (Linear.Ident -> M Linear.Term) -> M Linear.Term
result m f = N $ \ k1 k2 -> runN m (\ d1 k2 -> runN (f d1) (\ t1 k2 -> k2 t1) k2) k2

newtype N a b = N { runN :: (b -> (a -> M Simple.Program) -> M Simple.Program) -> (a -> M Simple.Program) -> M Simple.Program }

type M a = N Linear.Term a

instance Monad (N a) where
  return x = N $ \ k1 k2 -> k1 x k2
  m >>= f = N $ \ k1 k2 -> runN m (\ x k2 -> runN (f x) k1 k2) k2
