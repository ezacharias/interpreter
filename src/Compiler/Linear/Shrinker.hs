-- Let's work on this incrementally.
--   1. Do nothing but rename.
--   2. Attempt to drop unused instructions.
--   3. Use values.
--   4. Attempt to inline the continuation for case.
--   5. Attempt to inline functions.

module Compiler.Linear.Shrinker where

import Control.Applicative ((<|>), empty)

import Compiler.Linear

shrink :: Program -> Program
shrink = undefined

rename :: Ident -> M Ident
rename = undefined

gen :: M Ident
gen = undefined

getValue :: Ident -> M Value
getValue = undefined

data Value =
   ClosureValue Ident Term
 | ConstructorValue Int [Ident]
 | UnknownValue

withContinuation :: Ident -> Term -> M a -> M a
withContinuation = undefined

bindValue :: Ident -> Value -> M a -> M a
bindValue = undefined

shrinkTerm :: Term -> M Term

shrinkTerm (ApplyTerm d1 d2 d3 t1) = m1 <|> m2
  where m1 = do -- If we have a concrete type, attempt to inline it.
                d2' <- rename d2
                x <- getValue d2'
                case x of
                  ClosureValue d4 t2 -> do
                    x <- getValue d3
                    bindValue d4 x $ do
                      withContinuation d1 t1 $ do
                        shrinkTerm t2
                  _ -> empty
        m2 = do d1' <- gen
                d2' <- rename d2
                d3' <- rename d3
                t1' <- shrinkTerm t1
                bind d1' d1 $ do
                  return $ ApplyTerm d1' d2' d3' t1'
shrinkTerm (CaseTerm d1 d2 c1s t1) = do
  d2' <- rename d2
  x <- getValue d2
  case x of
    ConstructorValue i d3s' -> do
      withContinuation d1 t1 $ do
        (d3s, t2) <- return $ c1s !! i
        binds d3s d3s' $ do
          shrinkTerm t2
    _ -> m1 <|> m2
  where m1 = do -- If the continuation is not already a ReturnTerm, attepmt to inline it.
                case t1 of
                  ReturnTerm _ ->
                    empty
                  _ ->
                    return ()
                withContinuation d1 t1 $ do
                  c1s' <- shrinkRules c1s
                  return $ CaseTerm d1 d2 c1s'
                         $ ReturnTerm d1
        m2 = do c1s' <- withK (\ d -> return $ ReturnTerm d) $ do
                          shrinkRules c1s
                bind undefined undefined $ do
                  t1' <- shrinkTerm t1
                  return $ CaseTerm d1 d2 c1s' t1'
shrinkTerm (ConstructorTerm d1 d2 i d3s t) = do
  -- Add the constructor to the values.
  bindValue d1 (ConstructorValue i d3s) $ do
    m1 <|> m2
  where m1 = shrinkTerm t
        m2 = bind undefined undefined $ do
               increment 1
               t' <- shrinkTerm t
               return $ undefined
shrinkTerm (LambdaTerm d1 d2 ty1 t1 t2) =
  -- Add the lambda to the values.
  bindValue d1 undefined $ do
    m1 <|> m2
  where m1 = shrinkTerm t2
        m2 = do d2' <- gen
                t1' <- bind d2 d2' $ do
                         shrinkTerm t1
                d1' <- gen
                t2' <- bind d1 d1' $ do
                         shrinkTerm t2
                return $ LambdaTerm d1' d2' ty1 t1' t2'
shrinkTerm (ReturnTerm d) = do
  -- Fetch the return function and pass it the ident.
  return $ undefined
shrinkTerm (StringTerm d1 x1 t1) = m1 <|> m2
  where m1 = shrinkTerm t1
        m2 = bind undefined undefined $ do
               increment 1
               t1' <- shrinkTerm t1
               return $ StringTerm d1 x1 t1'
shrinkTerm (ThrowTerm d1 d2 d3 t1) = m1 <|> m2
  where m1 = undefined
        m2 = do -- 
                t1' <- shrinkTerm t1
                return $ ThrowTerm d1 d2 d3 t1
shrinkTerm (TupleTerm d1 d2s t1) = m1 <|> m2
  where m1 = do -- bind the tuple value so it can be used in an untuple
                -- but do not allow it to be used anywhere else
                shrinkTerm t1
        m2 = do -- bind the tuple value so it can be used in an untuple
                -- and also allow it to be used elsewhere
                bind undefined undefined $ do
                  increment 1
                  t1' <- shrinkTerm t1
                  return undefined
shrinkTerm (UntupleTerm d1s d2 t1) = m1 <|> m2
  where m1 = do -- if we have the concrete value, bind those
                -- if not, simply ingore it.
                shrinkTerm t1
        m2 = do -- bind the identifiers to the untuple
                binds undefined undefined $ do
                  t1' <- shrinkTerm t1
                  return $ undefined
{-
shrinkTerm (UpperTerm d1 d2 t1) = m1 <|> m2
  where m1 = pushK d1 t1 $ do
               t2 <- getFun d2
               -- We need to avoid infinite recursion here.
               shrinkTerm t2
        m2 = bind d1 d1 $ do
               t1' <- shrinkTerm t1
               return $ UpperTerm d1 d2 t1'
-}
shrinkTerm _ = undefined

withK :: (Ident -> M Term) -> M a -> M a
withK = undefined

shrinkRules :: [([Ident], Term)] -> M [([Ident], Term)]
shrinkRules = undefined

pushK :: Ident -> Term -> M a -> M a
pushK = undefined

getFun :: Ident -> M Term
getFun = undefined

binds :: [Ident] -> [Ident] -> M a -> M a
binds = undefined

bind :: Ident -> Ident -> M a -> M a
bind = undefined

increment :: Int -> M ()
increment = undefined

type M a = [a]
