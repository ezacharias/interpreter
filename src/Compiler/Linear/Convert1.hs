module Compiler.Linear.Convert1 where

import Compiler.Linear as Linear


type M a = [a]

convertTerm :: Linear.Term -> Linear.Ident -> M Linear.Term
convertTerm t d0 =
  case t of
    Linear.ApplyTerm d1s d2 d3s (Linear.ReturnTerm d4s) | d1s == d4s -> do
      d5 <- gen
      return $ Linear.ApplyTerm [d5] d2 d3s
             $ Linear.ReturnTerm [d5]
    Linear.ApplyTerm d1s d2 d3s t1 -> do
      d4 <- gen
      d5 <- gen
      t1' <- convertTerm t1 d5
      return $ Linear.LambdaTerm d4 (d1s ++ [d5]) undefined t1'
             $ Linear.ReturnTerm [d4]
    Linear.CatchTerm d1 d2 d3 t1 t2 -> do
      d4 <- gen
      d5 <- gen
      d6 <- gen
      d7 <- gen
      t1' <- convertTerm t1 d4
      -- t2' <- convertTerm t2 d0 \ d8 -> $
      --   return $ Linear.ApplyTerm _ d0 [d8]
      -- t1' <- convertTerm t1 ? \ d6 -> $
      --   return $ Linear.CaseTerm d6 [([d7], t2')]
      return $ Linear.LambdaTerm d4 [d5] undefined (Linear.ReturnTerm [d5])
             $ Linear.LambdaTerm d6 [] [] t1'
             $ Linear.ApplyTerm [d7] d6 []
             $ Linear.CaseTerm d7 []

    Linear.LambdaTerm d1 d2s _ t1 t2 -> do
      d3 <- gen
      t1' <- convertTerm t1 d3
      t2' <- convertTerm t2 d0
      return $ Linear.LambdaTerm d1 (d2s ++ [d3]) undefined t1' t2'
    Linear.ReturnTerm d1s -> do
      d2 <- gen
      return $ Linear.ApplyTerm [d2] d0 d1s
             $ Linear.ReturnTerm [d2]
    Linear.StringTerm d1 s1 t1 -> do
      t1' <- convertTerm t1 d0
      return $ Linear.StringTerm d1 s1 t1
    Linear.ThrowTerm d1 d2 d3 t1 -> do
      d4 <- gen
      d5 <- gen
      t1' <- convertTerm t1 d0
      return $ Linear.LambdaTerm d4 [d1] undefined t1'
             $ Linear.ConstructorTerm d5 undefined undefined [d3, d4]
             $ Linear.ReturnTerm [d5]
    Linear.UnreachableTerm ty1 ->
      return $ Linear.UnreachableTerm ty1
    _ -> undefined

gen :: M Linear.Ident
gen = undefined
