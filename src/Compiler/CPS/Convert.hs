module Compiler.CPS.Convert where

import qualified Compiler.Simple as Simple
import qualified Compiler.CPS as CPS

convertSimpleToCPS :: Simple.Program -> CPS.Program
convertSimpleToCPS = todo "convertSimpleToCPS"


withContinuation :: Simple.Ident -> M a -> M a
withContinuation = todo "withContinuation"

convertTerm :: Simple.Term -> M CPS.Ident
convertTerm t =
  case t of
    Simple.CatchTerm d1 d2 t1 -> do
      -- ^ Tag, Sum type, Body, Handler Closure
      d3 <- convertTerm t1
      t2 <- (todo "convertTerm") d3
      d4 <- gen
      withContinuation d4 $ do
        d5 <- convertTerm t1
        -- LambdaTerm [Ident] [Type] Term (Ident, Term)
        d6 <- gen
        returnTail $ CPS.LambdaTerm [] [] d5 (d6, CPS.CaseTerm [...])
        todo "convertTerm"
    Simple.ThrowTerm d1 t1 -> do
      d2 <- convertTerm t1
      ty1 <- getIdentType d2
      sumIdent <- todo "convertTerm"
      index <- todo "convertTerm"
      withTailFunction $ \ d3 -> do
        constructorIdent <- gen
        continuationIdent <- getContinuationIdent
        returnTail $ CPS.ConstructorTerm sumIdent index [d2, d3]
          (constructorIdent, CPS.ApplyTerm continuationIdent [constructorIdent])
    Simple.UnitTerm -> do
      k1 <- todo "convertTerm"
      d1 <- gen
      returnTail $ CPS.UnitTerm (d1, k1 d1)
    _ -> todo "convertTerm"

getIdentType :: CPS.Ident -> M CPS.Type
getIdentType = todo "getIdentType"

returnTail :: CPS.Term -> M CPS.Ident
returnTail = todo "tail"

gen :: M CPS.Ident
gen = todo "gen"

getContinuationIdent :: M CPS.Ident
getContinuationIdent = todo "getContinuationIdent"

withTailFunction :: (CPS.Ident -> M a) -> M a
withTailFunction = todo "withContinuation"


type M a = [a]


-- Utility Functions

todo :: String -> a
todo s = error $ "todo: CPS.Convert." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: CPS.Convert." ++ s
