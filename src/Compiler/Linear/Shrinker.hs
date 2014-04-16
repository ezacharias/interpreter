module Compiler.Linear.Shrinker where

import Control.Monad (forM)

import Compiler.Linear

shrink :: Program -> Program
shrink = todo "shrink"

type M a = [a]

-- We could record pure functions and pure closures for dropping.
-- Drop case statements whose bodies cannot throw to it.
-- Correctly deal with throws to case statements in lexical scope.

-- Uncurrying.

shrinkFun :: Fun -> M Fun
shrinkFun (Fun d1s ty1s ty2s t1) = do
  d1s' <- mapM (const gen) d1s
  t1' <- withBinds d1s d1s' (map (const OpaqueValue) d1s') $
           shrinkTerm t1
  return $ Fun d1s' ty1s ty2s t1'

shrinkTerm :: Term -> M Term
shrinkTerm t =
  case t of
    ApplyTerm d1s d2 d3s t1 -> do
      d1s' <- mapM (const gen) d1s
      d2' <- rename d2
      d3s' <- mapM rename d3s
      v1 <- getValue d2'
      case v1 of
        ClosureValue d3s _ t2 -> do
          v3s <- mapM getValue d3s'
          withBinds d3s d3s' v3s $
            withComposedContinuation (\ d1s' v1s -> withBinds d1s d1s' v1s (shrinkTerm t1)) $ do
              shrinkTerm t2
        OpaqueValue -> do
          t1' <- withBinds d1s d1s' (map (const OpaqueValue) d1s') $
            shrinkTerm t1
          incApplied d2'
          mapM_ incUsed d3s'
          return $ ApplyTerm d1s' d2' d3s' t1'
        _ ->
          unreachable "shrinkTerm"
    CallTerm d1s d2 d3s t1 -> do
      d1s' <- mapM (const gen) d1s
      d3s' <- mapM rename d3s
      t1' <- withBinds d1s d1s' (map (const OpaqueValue) d1s') $
        shrinkTerm t1
      mapM_ incUsed d3s'
      return $ CallTerm d1s' d2 d3s' t1'
    CaseTerm d1s d2 r1s t1 -> do
      d1s' <- mapM (const gen) d1s
      d2' <- rename d2
      v2 <- getValue d2'
      case v2 of
        ConstructorValue i1 d3s' -> do
          (d3s, t2) <- return $ r1s !! i1
          v3s <- mapM getValue d3s'
          t2' <- withComposedContinuation (\ d1s' v1s -> withBinds d1s d1s' v1s $ shrinkTerm t1) $
            withBinds d3s d3s' v3s $
              shrinkTerm t2
          mapM_ incUsed d3s'
          return t2'
        OpaqueValue -> do
          r1s' <- forM r1s $ \ (d3s, t2) -> do
            d3s' <- mapM (const gen) d3s
            t2' <- withBinds d3s d3s' (map (const OpaqueValue) d3s') $
                     withContinuation zeroContinuation $
                       shrinkTerm t2
            return (d3s', t2')
          t1' <- withBinds d1s d1s' (map (const OpaqueValue) d1s') $
            shrinkTerm t1
          incUsed d2'
          return $ CaseTerm d1s' d2' r1s' t1'
        _ ->
          unreachable "shrinkTerm"
    CatchTerm d1 d2 d3 t1 t2 -> do
      d1' <- gen
      t1' <- shrinkTerm t1
      t2' <- withBind d1 d1' OpaqueValue $
        shrinkTerm t2
      return $ CatchTerm d1' d2 d3 t1' t2'
    ConcatenateTerm d1 d2 d3 t1 -> do
      d1' <- gen
      d2' <- rename d2
      d3' <- rename d3
      withBind d1 d1' OpaqueValue $ do
        t1' <- shrinkTerm t1
        b <- isUsed d1'
        if b
          then do
            incUsed d2'
            incUsed d3'
            return $ ConcatenateTerm d1' d2' d3' t1'
          else
            return t1'
    ConstructorTerm d1 d2 i1 d3s t1 -> do
      d1' <- gen
      d3s' <- mapM rename d3s
      withBind d1 d1' (ConstructorValue i1 d3s') $ do
        t1' <- shrinkTerm t1
        b <- isUsed d1'
        if b
          then do
            mapM_ incUsed d3s'
            return $ ConstructorTerm d1' d2 i1 d3s' t1'
          else
            return t1'
    LambdaTerm d1 d2s ty1s t1 t2 -> do
      d1' <- gen
      m <- withBind d1 d1' OpaqueValue $ do
        t2' <- shrinkTerm t2
        i <- getUseCount d1'
        return $ case i of
                   0 -> do
                     return t2'
                   1 -> do
                     withBind d1 d1' (ClosureValue d2s ty1s t1) $ do
                       shrinkTerm t2
                   _ -> do
                     d2s' <- mapM (const gen) d2s
                     t1' <- withBinds d2s d2s' (map (const OpaqueValue) d2s') $
                              withContinuation zeroContinuation $
                                shrinkTerm t1
                     return $ LambdaTerm d1' d2s' ty1s t1' t2'
      m
    ReturnTerm d1s -> do
      continue d1s
    StringTerm d1 s1 t1 -> do
      d1' <- gen
      withBind d1 d1' OpaqueValue $ do
        t1' <- shrinkTerm t1
        b <- isUsed d1'
        if b
          then do
            return $ StringTerm d1' s1 t1'
          else
            return t1'
    ThrowTerm d1 d2 d3 t1 -> do
      d1' <- gen
      d3' <- rename d3
      t1' <- withBind d1 d1' OpaqueValue $
        shrinkTerm t1
      incUsed d3'
      return $ ThrowTerm d1' d2 d3' t1'
    TupleTerm d1 d2s t1 -> do
      d1' <- gen
      d2s' <- mapM rename d2s
      withBind d1 d1' (TupleValue d2s') $ do
        t1' <- shrinkTerm t1
        b <- isUsed d1'
        if b
          then do
            mapM_ incUsed d2s'
            return $ TupleTerm d1' d2s' t1'
          else
            return t1'
    UnreachableTerm ty1 ->
      -- There is no need to continue from this point because the program will
      -- terminate. However, we need the return type of the tail.
      return $ UnreachableTerm (todo "shrinkTerm")
    UntupleTerm d1s d2 t1 -> do
      d2' <- rename d2
      v2 <- getValue d2
      case v2 of
        TupleValue d1s' -> do
          v1s <- mapM getValue d1s'
          withBinds d1s d1s' v1s $
            shrinkTerm t1
        OpaqueValue -> do
          d1s' <- mapM (const gen) d1s
          withBinds d1s d1s' (map (const OpaqueValue) d1s) $ do
            t1' <- shrinkTerm t1
            bs <- mapM isUsed d1s'
            if (or bs)
              then do
                incUsed d2'
                return $ UntupleTerm d1s' d2' t1'
              else
                return t1'
        _ ->
          unreachable "shrinkTerm"

getUseCount :: Ident -> M Int
getUseCount = todo "getUseCount"

incApplied :: Ident -> M ()
incApplied = todo "incApplied"

incUsed :: Ident -> M ()
incUsed = todo "incUsed"

isUsed :: Ident -> M Bool
isUsed = todo "isUsed"

-- Because of alpha renaming, we can shrink the tail without worrying about
-- naming conflicts.
withComposedContinuation :: ([Ident] -> [Value] -> M Term) -> M Term -> M Term
withComposedContinuation k2 m = do
  k1 <- getContinuation
  let k3 d1s v1s =
        withContinuation k2 $
          k1 d1s v1s
  withContinuation k3 m

zeroContinuation :: [Ident] -> [Value] -> M Term
zeroContinuation d1s' v1s = do
  mapM_ incUsed d1s'
  return $ ReturnTerm d1s'

continue :: [Ident] -> M Term
continue d1s = do
  d1s' <- mapM rename d1s
  v1s <- mapM getValue d1s'
  k <- getContinuation
  k d1s' v1s


getContinuation :: M ([Ident] -> [Value] -> M Term)
getContinuation = todo "getContinuation"

withContinuation :: ([Ident] -> [Value] -> M Term) -> M Term -> M Term
withContinuation = todo "withContinuation"

getValue :: Ident -> M Value
getValue = todo "getValue"

gen :: M Ident
gen = todo "gen"

rename :: Ident -> M Ident
rename = todo "rename"

data Value =
   ClosureValue [Ident] [Type] Term
 | ConstructorValue Int [Ident]
 | OpaqueValue
 | TupleValue [Ident]

withBind :: Ident -> Ident -> Value -> M a -> M a
withBind = todo "withBind"

withBinds :: [Ident] -> [Ident] -> [Value] -> M a -> M a
withBinds = todo "withBinds"


{-
    ApplyTerm d1s d2 d3s t1 -> do
      -- check if d1s should be inlined
      -- record d1s as unknown values
      -- record d2 as used
      -- record d3s as used
      t1' <- shrinkTerm t1
      return $ ApplyTerm d1s d2 d3s t1'
    CaseTerm d1s d2 r1s t1 -> do
      v1 <- getValue d2
      case v1 of
        ConstructorValue i1 d3s -> do
          (d4s, t2) <- return $ r1s !! i1
          withRename d4s d3s $
            shrinkTerm t1
        OpaqueValue -> do
          ms <- forM r1s $ \ (d3s, t2) ->
            reset $ do
              t2' <- withBinds d3s (repeat OpaqueValue) $
                shrinkTerm t2
              return (d3s, t2')
          r1s' <- sequence ms
          t1' <- withBinds d1s (repeat OpaqueValue) $
            shrinkTerm t1
          return $ CaseTerm d1s d2 r1s' t1'
        _ ->
          unreachable "shrinkTerm"
    LambdaTerm d1 d2s ty1s t1 t2 ->
      withBind d1 (ClosureValue d2s ty1s t1) $ do
        t2' <- shrinkTerm t2
        b <- isUsed d1
        if b then do t1' <- withBinds d2s (repeat OpaqueValue) $
                              shrinkTerm t1
                     return $ LambdaTerm d1 d2s ty1s t1' t2'
             else return t2'
    ReturnTerm d1s -> do
      d1s' <- mapM rename d1s
      mapM_ incUsed d1s'
      shift $ do
        return $ ReturnTerm d1s'
    StringTerm d1 s1 t1 ->
      -- d1' <- gen
      withBind d1 OpaqueValue $ do
        t1' <- shrinkTerm t1
        b <- isUsed d1
        return $ if b then StringTerm d1 s1 t1' else t1'
    UnreachableTerm ty ->
      return $ UnreachableTerm ty
    _ ->
      todo "shrinkTerm"
-}


{-

getValue :: Ident -> M Value
getValue = todo "getValue"

-- Finish analysis before returning.
shift :: M Term -> M Term
shift = todo "shift"

reset :: M a -> M (M a)
reset = todo "reset"

incUsed :: Ident -> M ()
incUsed = todo "setUsed"

isUsed :: Ident -> M Bool
isUsed = todo "isUsed"

withBinds :: [Ident] -> [Value] -> M a -> M a
withBinds = todo "withBind"

withBind :: Ident -> Value -> M a -> M a
withBind = todo "withBind"

withRename :: [Ident] -> [Ident] -> M a -> M a
withRename = todo "withRename"

-}


-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Linear.Shrinker." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Linear.Shrinker." ++ s
