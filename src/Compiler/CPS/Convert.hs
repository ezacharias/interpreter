module Compiler.CPS.Convert where

import Control.Monad (forM, forM_)
import qualified Data.IntMap as IntMap

import qualified Compiler.Simple as Simple
import qualified Compiler.CPS as CPS

convertSimpleToCPS :: Simple.Program -> CPS.Program
convertSimpleToCPS p = run $ do

  forM_ (IntMap.toList (Simple.programFuns p)) $ \ (d, x) ->
    convertFun d x
  forM_ (IntMap.toList (Simple.programSums p)) $ \ (d, x) ->
    convertSum d x
  x1s <- get programSums
  x2s <- get programFuns
  return $ CPS.Program x1s x2s (Simple.programMain p)

convertSum :: Simple.Ident -> Simple.Sum -> M ()
convertSum d1 (Simple.Sum x1s) = do
  ty1s <- mapM (mapM convertType) x1s
  exportSum d1 (CPS.Sum ty1s)

-- We export functions rather than return them. A function takes a continuation
-- as an argument. All other arguments are curried for now.
convertFun :: Simple.Ident -> Simple.Fun -> M ()
convertFun d1 (Simple.Fun ty1 t1) = do
  ty2 <- convertType ty1
  d9 <- getResultTypeIdent ty2
  d0 <- gen
  ty0 <- return $ CPS.SumType d9
  t2 <- convertTerm t1 d0 $ \ d2 d0 -> do
    d3 <- gen
    return $ CPS.ConstructorTerm d3 d9 0 [d2] $
               CPS.ApplyTerm d0 [d3]
  exportFun d1 $ CPS.Fun [d0] [ty0] t2

-- d0 is the ident of the continuation function.
convertTerm :: Simple.Term -> CPS.Ident -> (CPS.Ident -> CPS.Ident -> M CPS.Term) -> M CPS.Term
convertTerm t d0 k =
  case t of
    Simple.ApplyTerm t1 t2 ->
      convertTerm t1 d0 $ \ d1 d0 ->
        convertTerm t2 d0 $ \ d2 d0 -> do
{-
          d3 <- gen
          -- This is not correct. We need to call a top-level handling function to check the result object.
          d4 <- gen
          t3 <- k d4 d0
          return $ CPS.LambdaTerm d3 [d4] [todo "convertTerm"] t3 $
                     CPS.ApplyTerm d1 [d2, d3]
-}
          u
    Simple.BindTerm d1 t1 t2 ->
      convertTerm t1 d0 $ \ d2 d0 ->
        bind d1 d2 $
          convertTerm t2 d0 k
    Simple.CaseTerm t1 c1s ->
      convertTerm t1 d0 $ \ d1 d0 -> do
        d2 <- gen
        d3 <- gen
        d4 <- gen
        t2 <- k d3 d4
        c2s <- forM (zip [0..] c1s) $ \ (i1, (d5s, t3)) -> do
          foo i1
          t4 <- convertTerm t3 d0 (\ d6 d0 -> return $ CPS.ApplyTerm d2 [d6, d0])
          return $ (d5s, t4)
        return $ CPS.LambdaTerm d2 [d3, d4] [u, u] t2 $
                   CPS.CaseTerm d1 c2s
    Simple.CatchTerm d1 d2 t1 -> do
      d3 <- gen
      d7 <- gen
      t2 <- k d3 d7
      d4 <- gen
      t3 <- convertTerm t1 d4 $ \ d5 d0 -> do
        d6 <- gen
        return $ CPS.ConstructorTerm d6 u 0 [d5] $
                   CPS.ApplyTerm d0 [d6]
      d5 <- gen
      d6 <- gen
      -- This is the top-level function which handles the result.
      d8 <- gen
      return $ CPS.LambdaTerm d4 [d5] [u]
                   (CPS.LambdaTerm d6 [d3, d7] u t2 $
                     CPS.CallTerm d8 [d5, d6, d0])
                 t3
    Simple.FunTerm d1 -> do
      d2 <- gen
      d3 <- gen
      d4 <- gen
      d5 <- gen
      t2 <- k d3 d5
      -- This is the top-level function which handles the result.
      d8 <- gen
      return $ CPS.LambdaTerm d2 [d3] u
                   (CPS.LambdaTerm d4 [d3, d5] u t2 $
                     CPS.CallTerm d8 [d4, d4, d0]) $
                 CPS.CallTerm d1 [d2]
    Simple.LambdaTerm d1 ty1 t1 -> do
      d2 <- gen
      d3 <- gen
      t2 <- convertTerm t1 d3 $ \ d4 d3 -> do
              d5 <- gen
              return $ CPS.ConstructorTerm d5 u 0 [d4] $
                         CPS.ApplyTerm d3 [d5]
      t3 <- k d2 d0
      return $ CPS.LambdaTerm d2 [d1, d3] [u] t2
                 t3
    Simple.ThrowTerm d1 t1 ->
      convertTerm t1 d0 $ \ d2 d0 -> do
        d3 <- gen
        d4 <- gen
        d5 <- gen
        t2 <- k d4 d5
        d6 <- gen
        return $ CPS.LambdaTerm d3 [d4, d5] [u] t2 $
                   CPS.ConstructorTerm d6 u u [d2, d3] $
                     CPS.ApplyTerm d0 [d6]
    Simple.UnreachableTerm ty1 ->
      return $ CPS.UnreachableTerm u
    Simple.VariableTerm d1 -> do
      d2 <- getIdent d1
      k d2 d0
    _ ->
      todo "convertTerm"













-- Returns the sum type identifier for the type. If it does not exist, it is
-- generated. Each escape has two types, which we use to generate every case and the normal case.
getResultTypeIdent :: CPS.Type -> M CPS.Ident
getResultTypeIdent = todo "getContinuationType"

-- Returns the identifier of the continuation handler function.
getContinuationHandler :: CPS.Ident -> M CPS.Ident
getContinuationHandler = todo "getContinuationHandler"


-- A hanlder function takes a continuation, a delimited function, and a result object.
genContinuationHandler :: CPS.Ident -> CPS.Type -> M ()
genContinuationHandler d1 ty1 = do
  d2 <- gen
  d3 <- gen
  d4 <- gen
  c1 <- do
    d5 <- gen
    return ([d5], CPS.ApplyTerm d3 [d5, d4])
  ty2s <- getEscapeTypes
  c1s <- forM (zip [1..] ty2s) $ \ (i1, (ty2, ty3)) -> do
           d5 <- gen
           d6 <- gen
           d7 <- gen
           d8 <- gen
           d9 <- gen
           d10 <- gen
           d11 <- gen
           d12 <- gen
           t1 <- return $ CPS.LambdaTerm d8 [d9, d10] [ty2, u]
                              (CPS.LambdaTerm d11 [d12] [u]
                                  -- Crazy recursive result handling.
                                  (CPS.CallTerm d1 [d12, d3, d4]) $
                                CPS.ApplyTerm d6 [d9, d11]) $
                            CPS.ConstructorTerm d7 u i1 [d5, d8] $
                              CPS.ApplyTerm d4 [d7]
           return ([d5, d6], t1)
  d5 <- getResultTypeIdent ty1
  x1 <- return $ CPS.Fun [d2, d3, d4] [u, u, u] $
                   CPS.CaseTerm d2 (c1:c1s)
  exportFun d1 x1

getEscapeTypes :: M [(CPS.Type, CPS.Type)]
getEscapeTypes = todo "getEscapeTypes"










exportSum :: CPS.Ident -> CPS.Sum -> M ()
exportSum = todo "exportSum"

exportFun :: CPS.Ident -> CPS.Fun -> M ()
exportFun = todo "exportFun"

convertType :: Simple.Type -> M CPS.Type
convertType ty =
  case ty of
    Simple.ArrowType ty1 ty2 -> do
      ty3 <- convertType ty1
      ty4 <- convertType ty2
      d1 <- getResultTypeIdent ty4
      return $ CPS.ClosureType [ty3, CPS.ClosureType [CPS.SumType d1]]
    Simple.StringType ->
      return CPS.StringType
    Simple.TupleType ty1s -> do
      ty2s <- mapM convertType ty1s
      return $ CPS.TupleType ty2s
    Simple.UnitType ->
      return $ CPS.TupleType []
    Simple.SumType d ->
      return $ CPS.SumType d

run :: M a -> a
run = todo "run"

gen :: M CPS.Ident
gen = todo "gen"

data Result =
   Static CPS.Ident
 | Dynamic CPS.Ident

bind :: Simple.Ident -> CPS.Ident -> M a -> M a
bind = todo "bind"

foo :: Int -> M ()
foo = todo "foo"

getIdent :: Simple.Ident -> M CPS.Ident
getIdent = todo "getIdent"

getHandler :: [CPS.Type] -> M CPS.Ident
getHandler ty1s = todo "getHandler"

type M a = [a]

u :: a
u = undefined

get :: (State -> a) -> M a
get = todo "get"

data State = State
  { programSums :: CPS.IdentMap CPS.Sum
  , programFuns :: CPS.IdentMap CPS.Fun
  }

{-

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

-}

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: CPS.Convert." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: CPS.Convert." ++ s
