-- The job of this pass is to remove Catch and Throw.


module Compiler.Handling where

import qualified Compiler.Simple as Simple

convert :: Simple.Program -> Simple.Program
convert = todo "convert"

convertFun :: Simple.Fun -> M Simple.Fun
convertFun (Simple.Fun ty t) = todo "convertFun"

convertTerm :: Simple.Term -> M Simple.Term
convertTerm t =
  case t of
    Simple.ApplyTerm t1 t2 -> do
      t3 <- convertTerm t1
      t4 <- convertTerm t2
      d1 <- gen
      k1 <- todo "convertTerm"
      return $ Simple.ApplyTerm (todo "convertTerm") $
                 Simple.TupleTerm
                   [ Simple.ApplyTerm t3 t4
                   , Simple.LambdaTerm d1 (todo "convertTerm") (k1 d1)
                   ]
    Simple.LambdaTerm d1 ty1 t1 -> do
      d2 <- getResultSum ty1
      t2 <- convertTerm t1
      return $ Simple.LambdaTerm d1 (Simple.SumType d2) $
                 Simple.ConstructorTerm d2 0 [t2]
    Simple.UnitTerm -> do
      return $ Simple.UnitTerm
    _ ->
      todo "convertTerm"

getResultSum :: Simple.Type -> M Simple.Ident
getResultSum = todo "getResultType"

gen :: M Simple.Ident
gen = todo "gen"

type M a = [a]



-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Handling." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Handling." ++ s
