module Compiler.CPS.FromLinear where

import Compiler.CPS as CPS
import Compiler.Linear as Linear

convert :: Linear.Program -> CPS.Program
convert = undefined

type M a = [a]

convertTerm :: Linear.Term -> CPS.Ident -> CPS.Type -> CPS.Ident -> M CPS.Term
convertTerm t dk dkty dh =
  case t of
    Linear.ApplyTerm d1 d2 d3 t1 -> do
      d2' <- rename d2
      d3' <- rename d3
      continue d1 t1 dk dkty $ \ dk -> do
        return $ CPS.ApplyTerm d2' [d3', dk, dh]
    Linear.CatchTerm d1 d2 ty1 t1 t2 -> do
      d2' <- renameTag d2
      ty1' <- undefined
      -- we create a new dk which is just a function which creates a constructor and calls the handler.
      -- we create a new handler which calls a top-level function which has the case.
      undefined
    Linear.ReturnTerm d1 -> do
      d1' <- rename d1
      return $ CPS.ApplyTerm dk [d1', dh]
    Linear.ThrowTerm d1 d2 d3 t1 -> do
      d1' <- rename d1
      d2' <- renameTag d2
      d3' <- rename d3
      continue d1 t1 dk dkty $ \ dk ->
        return $ CPS.ApplyTerm dh [d2', dk]
    _ -> undefined

gen :: M CPS.Ident
gen = undefined

bind :: Linear.Ident -> CPS.Ident -> M CPS.Term -> M CPS.Term
bind = undefined

continue :: Linear.Ident -> Linear.Term -> CPS.Ident -> CPS.Type -> (CPS.Ident -> M CPS.Term) -> M CPS.Term
continue d1 (Linear.ReturnTerm d2) dk dkty f | d1 == d2 = f dk
continue d1 t1 dk dkty f = do
  d1' <- gen
  dh' <- gen
  t1' <- bind d1 d1' $ do
    convertTerm t1 dk dkty dh'
  dk' <- gen
  t2' <- f dk'
  return $ CPS.LambdaTerm dk' [d1', dh'] [dkty, undefined] t1' t2'

rename :: Linear.Ident -> M CPS.Ident
rename = undefined

renameTag :: Linear.Ident -> M CPS.Ident
renameTag = undefined

