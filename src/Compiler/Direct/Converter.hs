module Compiler.Direct.Converter where

import qualified Compiler.CPS as CPS
import qualified Compiler.Direct as Direct

convert :: CPS.Program -> Direct.Program
convert = undefined

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
    CPS.LambdaTerm d1 d2s ty2s t1 t2 -> do
      ty2s' <- mapM convertType ty2s
      d2s' <- mapM gen ty2s'
      d3' <- getClosureIdent ty2s'
      d1' <- gen (Direct.SumType d3')
      _ <- resetFree $ do
             t1' <- binds d2s d2s' $ do
                      convertTerm t1
             d4s' <- free
             undefined
      i <- undefined
      d4s' <- undefined
      t2' <- bind d1 d1' $ do
               convertTerm t2
      return $ Direct.ConstructorTerm d1' d3' i d4s' t2'
    _ ->
      undefined

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

resetFree :: M a -> M a
resetFree = undefined

free :: M [Direct.Ident]
free = undefined
