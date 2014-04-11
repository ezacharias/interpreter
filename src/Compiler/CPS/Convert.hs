module Compiler.CPS.Convert where

import qualified Compiler.Simple as Simple
import qualified Compiler.CPS as CPS

convertSimpleToCPS :: Simple.Program -> CPS.Program
convertSimpleToCPS = todo "convertSimpleToCPS"


withContinuation :: Simple.Ident -> M a -> M a
withContinuation = todo "withContinuation"

shiftTail :: CPS.Ident -> (Simple.Term -> M a) -> M a
shiftTail = todo "c"

getHandler :: CPS.Type -> M CPS.Ident
getHandler = todo "getHandler"

convertTerm :: Simple.Term -> M CPS.Ident
convertTerm t =
  case t of
    Simple.ApplyTerm t1 t2 -> do
      d1 <- convertTerm t1
      d2 <- convertTerm t2
      ty1 <- getIdentType d2
      d3 <- gen
      d4 <- gen
      -- This is the continuation handler
      d5 <- getHandler ty1
      d6 <- gen
      d7 <- gen
      d8 <- gen
      -- This is regular CPS. We want to have a case for a basic return.
      returnLet d3 $ \ t3 ->
        CPS.LambdaTerm d4 [d6] [todo "convertTerm"]
            (CPS.LambdaTerm d7 [d3, d8] [ty1] t3
              (CPS.CallTerm d5 [d6, d7])) $
          CPS.ApplyTerm d1 [d2, d4]
    Simple.CatchTerm d1 d2 t1 -> do
      -- ^ Tag, Sum type, Body, Handler Closure
      d3 <- convertTerm t1
      t2 <- (todo "convertTerm") d3
      d4 <- gen
      withContinuation d4 $ do
        d5 <- convertTerm t1
        -- LambdaTerm [Ident] [Type] Term (Ident, Term)
        d6 <- gen
        -- returnTail $ CPS.LambdaTerm [] [] d5 (d6, CPS.CaseTerm [...])
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

    Simple.TupleTerm t1s -> do
      d1s <- mapM convertTerm t1s
      d2 <- gen
      t2 <- todo "convertTerm"
      returnLet d2 $ CPS.TupleTerm d2 d1s
    Simple.UnitTerm -> do
      d1 <- gen
      returnLet d1 $ CPS.UnitTerm d1
    Simple.VariableTerm d1 -> do
      d2 <- getIdent d1 -- todo "convertTerm"
      returnLet d2 id
    _ ->
      todo "convertTerm"

getIdent :: Simple.Ident -> M CPS.Ident
getIdent = todo "getIdent"

returnLet :: CPS.Ident -> (CPS.Term -> CPS.Term) -> M CPS.Ident
returnLet = todo "floop"

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
