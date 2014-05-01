-- Lambda lifting.

module Compiler.Direct.Converter where

import Control.Monad (forM)

import qualified Compiler.CPS as CPS
import qualified Compiler.Direct as Direct

convert :: CPS.Program -> Direct.Program
convert p = run p $ do
  mapM_ convertSum (CPS.programSums p)
  mapM_ convertFun (CPS.programFuns p)
  finish
  x1s <- undefined
  x2s <- undefined
  d <- renameFunIdent (CPS.programStart p)
  return $ Direct.Program x1s x2s d

convertSum :: (CPS.Ident, CPS.Sum) -> M ()
convertSum = undefined

convertFun :: (CPS.Ident, CPS.Fun) -> M ()
convertFun = undefined

-- We now have the completed variant types, so we can generate them and the
-- apply functions.
finish :: M ()
finish = undefined

renameFunIdent :: CPS.Ident -> M Direct.Ident
renameFunIdent = undefined

run :: CPS.Program -> M a -> a
run = undefined

type M a = [a]

convertTerm :: CPS.Term -> M Direct.Term
convertTerm t =
  case t of
    CPS.ApplyTerm d1 d2s -> do
      d1' <- renameIdent d1
      Direct.SumType d3' <- getType d1'
      d2s' <- mapM renameIdent d2s
      ty2s' <- mapM getType d2s'
      d4' <- getApplyFun d3'
      return $ Direct.CallTerm d4' (d1':d2s')
    CPS.BindTerm d1 d2 t1 -> do
      d2' <- renameIdent d2
      bind d1 d2' $ do
        convertTerm t1
    CPS.ConcatenateTerm d1 d2 d3 t1 -> do
      d1' <- gen Direct.StringType
      d2' <- renameIdent d2
      d3' <- renameIdent d3
      bind d1 d1' $ do
        t1' <- convertTerm t1
        return $ Direct.ConcatenateTerm d1' d2' d3' t1'
    CPS.ExitTerm ->
      return Direct.ExitTerm
    CPS.LambdaTerm d1 d2s ty2s t1 t2 -> do
      ty2s' <- mapM convertType ty2s
      d3' <- getClosureIdent ty2s'
      d1' <- gen (Direct.SumType d3')
      d4s' <- resetFree $ do
                d2s' <- mapM gen ty2s'
                t1' <- binds d2s d2s' $ do
                         convertTerm t1
                d4s' <- free
                ty4s' <- mapM getType d4s'
                d5' <- getFunIdent
                exportFun (d5', Direct.Fun (d4s' ++ d2s') (ty4s' ++ ty2s') t1')
      i <- addConstructor d3' d4s'
      t2' <- bind d1 d1' $ do
               convertTerm t2
      return $ Direct.ConstructorTerm d1' d3' i d4s' t2'
    _ ->
      undefined

-- This takes:
--   d0      the name of the function to generate
--   sd      the ident of the sum type
--   ty2s    the types of the arguments to the closure
--   xs      the types of the free vars paired with the ident of the direct
--           function to call
createApplyFun :: Direct.Ident -> Direct.Ident -> [Direct.Type] -> [([Direct.Type], Direct.Ident)] -> M ()
createApplyFun d0 sd ty2s xs = do
  ty1 <- return $ Direct.SumType sd
  d1 <- gen ty1
  d2s <- mapM gen ty2s
  cs <- forM xs $ \ (ty3s, d4) -> do
          d3s <- mapM gen ty3s
          return $ (d3s, Direct.CallTerm d4 (d3s ++ d2s))
  exportFun (d0, Direct.Fun (d1:d2s) (ty1:ty2s) (Direct.CaseTerm d1 cs))

addConstructor :: Direct.Ident -> [Direct.Ident] -> M Int
addConstructor = undefined

getFunIdent :: M Direct.Ident
getFunIdent = undefined

exportFun :: (Direct.Ident, Direct.Fun) -> M ()
exportFun = undefined

getClosureIdent :: [Direct.Type] -> M Direct.Ident
getClosureIdent = undefined

convertType :: CPS.Type -> M Direct.Type
convertType = undefined

-- Returning from a bind must remove the ident from the use list.
bind :: CPS.Ident -> Direct.Ident -> M a -> M a
bind = undefined

binds :: [CPS.Ident] -> [Direct.Ident] -> M a -> M a
binds = undefined
-- Renaming must mark the ident as used.
renameIdent :: CPS.Ident -> M Direct.Ident
renameIdent = undefined

gen :: Direct.Type -> M Direct.Ident
gen = undefined

getType :: Direct.Ident -> M Direct.Type
getType = undefined

-- Uses the ident of the variant type for the closure.
getApplyFun :: Direct.Ident -> M Direct.Ident
getApplyFun = undefined

-- This is a tricky function. It must reset the free variable list.
-- Importantly, it must ensure the renames in the body are different from the
-- renames outside.
resetFree :: M () -> M [Direct.Ident]
resetFree = undefined

free :: M [Direct.Ident]
free = undefined
