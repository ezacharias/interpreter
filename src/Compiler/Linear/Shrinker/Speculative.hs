module Compiler.Linear.Shrinker.Speculative where

-- The speculative shrinker will attempt to inline within a function, falling
-- back to not inlining if the function does not become smaller. We must be
-- careful to manually check for infinite recursion and fail if it occurs.

import Compiler.Linear

-- Returns the modified program if it has been modified or returns Nothing if
-- there are no modifications.
shrink :: Program -> Maybe Program
shrink p = Nothing

{-

run :: M Program -> Program
run = undefined

data M a = Recursion
         | Normal Int a

instance Monad M where
  return x = Normal 0 x
  m >>= f = undefined

increment :: Int -> M a -> M a
increment i0 (Recursion) = Recursion
increment i0 (Normal i1 x) = Normal (i0 + i1) x

shrinkRule :: ([Ident], Term) -> ([Ident] -> M Term) -> M ([Ident], Term)
shrinkRule = undefined

shrinkTerm :: Term -> ([Ident] -> M Term) -> M Term
shrinkTerm t k =
  case t of
    ApplyTerm d1s d2 d3s t1 ->
      undefined
    CallTerm d1s d2 d3s t ->
      withRenames d1s $ \ d1s' ->
        increment 1 $ do
          d3s' <- mapM rename d3s
          t1' <- shrinkTerm t k
          return $ CallTerm d1s' d2 d3s' t1'
    CaseTerm d1s d2s c1s (ReturnTerm d3s) | d1s == d3s -> do
      c1s' <- mapM (flip shrinkRule emptyK) c1s
      return $ CaseTerm d1s d2s c1s (ReturnTerm d3s)
    CaseTerm d1s d2s c1s t1 ->
      let m1 = do c1s' <- mapM (flip shrinkRule (\ _ -> shrinkTerm t1 k)) c1s
                  return $ CaseTerm d1s d2s c1s' (ReturnTerm d1s)
          m2 = do c1s' <- mapM (flip shrinkRule emptyK) c1s
                  t1' <- shrinkTerm t1 k
                  return $ CaseTerm d1s d2s c1s' t1'
       in contrast m1 m2
    LambdaTerm d1 d2s ty2s t1 t2 -> do
      join $ withRename d1 $ \ d1' -> do
               t2' <- shrinkTerm t2 k
               b <- isUsed [d1']
               if not b
                 then return $ return t2'
                 else let m1 = withRenames d2s $ \ d2s' -> do
                                 t1' <- shrinkTerm t1 emptyK
                                 return $ LambdaTerm d1' d2s' ty2s t1' t2'
                          m2 = do withClosure d1 d2s ty2s t1 $ do
                                    shrinkTerm t2 k
                       in return $ contrast m1 m2
    ReturnTerm ds ->
      k ds
    StringTerm d s t ->
      withRename d $ \ d' -> do
        t' <- shrinkTerm t k
        b <- isUsed [d']
        if b
          then increment 1 $ do
                 return $ StringTerm d' s t'
          else return t'
    _ -> undefined

contrast :: M a -> M a -> M a
contrast x y = undefined

withClosure :: Ident -> [Ident] -> [Type] -> Term -> M a -> M a
withClosure = undefined

emptyK :: [Ident] -> M Term
emptyK ds = do
  ds' <- mapM rename ds
  return $ ReturnTerm ds'

isUsed :: [Ident] -> M Bool
isUsed = undefined

withRename :: Ident -> (Ident -> M a) -> M a
withRename = undefined

withRenames :: [Ident] -> ([Ident] -> M a) -> M a
withRenames = undefined

rename :: Ident -> M Ident
rename = undefined

-}
