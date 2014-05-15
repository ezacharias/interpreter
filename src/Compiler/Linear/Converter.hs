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
convertTerm (Simple.StringTerm x1) = do
  d1' <- gen
  continue d1' $ \ t1' -> do
    return $ Linear.StringTerm d1' x1 t1'
convertTerm (Simple.LambdaTerm d1 ty1 t1) = do
  d1' <- gen
  d2' <- gen
  ty1' <- undefined
  t1' <- result (bind d1 d1' (convertTerm t1)) (\ d -> return $ Linear.ReturnTerm d)
  continue d2' $ \ t2' -> do
    return $ Linear.LambdaTerm d2' d1' ty1' t1' t2'
convertTerm (Simple.VariableTerm d1) = do
  rename d1
convertTerm _ =
  undefined

rename :: Simple.Ident -> M Linear.Ident
rename = undefined

bind :: Simple.Ident -> Linear.Ident -> M Simple.Ident -> M Linear.Ident
bind d1 d2 m = undefined

continue :: Linear.Ident -> (Linear.Term -> M Linear.Term) -> M Linear.Ident
continue d f = N $ \ k1 k2 -> k1 d (\ t -> runN (f t) (\ t k2 -> k2 t) k2)

result :: M Simple.Ident -> (Linear.Ident -> M Linear.Term) -> M Linear.Term
result m f = N $ \ k1 k2 -> runN m (\ d1 k2 -> runN (f d1) (\ t1 k2 -> k2 t1) k2) k2

newtype N a b = N { runN :: (b -> (a -> M Simple.Program) -> M Simple.Program) -> (a -> M Simple.Program) -> M Simple.Program }

type M a = N Linear.Term a

instance Monad (N a) where
  return x = N $ \ k1 k2 -> k1 x k2
  m >>= f = N $ \ k1 k2 -> runN m (\ x k2 -> runN (f x) k1 k2) k2
