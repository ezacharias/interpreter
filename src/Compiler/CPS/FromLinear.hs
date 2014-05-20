module Compiler.CPS.FromLinear where

import qualified Compiler.CPS as CPS
import qualified Compiler.Linear as Linear

convert :: Linear.Program -> CPS.Program
convert p = run p $ do
  -- _ <- error $ show (Simple.programTags p)
  mapM_ convertSum (Linear.programSums p)
  mapM_ convertFun (Linear.programFuns p)
  d  <- createStartFun (Linear.programMain p)
  createResultSum
  x1 <- get programSums
  x2 <- get programFuns
  return $ CPS.Program x1 x2 d

convertSum :: (Linear.Ident, Linear.Sum) -> M ()
convertSum (d0, Linear.Sum tyss) = do
  tyss' <- mapM (mapM convertType) tyss
  d0' <- renameSumIdent d0
  exportSum (d0', CPS.Sum tyss')

getHandlerType :: M CPS.Type
getHandlerType = do
  d <- getResultTypeIdent
  return $ CPS.ArrowType [CPS.SumType d]

-- Returns the sum type ident for Result.
getResultTypeIdent :: M CPS.Ident
getResultTypeIdent = do
  look resultIdent

convertType :: Linear.Type -> M CPS.Type
convertType ty =
  case ty of
    Linear.ArrowType ty1 ty2 -> do
      ty0' <- getHandlerType
      ty1' <- convertType ty1
      ty2' <- convertType ty2
      return $ CPS.ArrowType [ty1', CPS.ArrowType [ty2', ty0'], ty0']
    Linear.StringType ->
      return $ CPS.StringType
    Linear.TupleType tys -> do
      tys' <- mapM convertType tys
      return $ CPS.TupleType tys'
    Linear.SumType d1 -> do
      d1' <- renameSumIdent d1
      return $ CPS.SumType d1'

renameSumIdent :: Linear.Ident -> M CPS.Ident
renameSumIdent d = do
  xs <- get sumIdentRenames
  case lookup d xs of
    Nothing -> do
      d' <- gen
      set $ \ s -> s {sumIdentRenames = (d,d'):xs}
      return d'
    Just d' ->
      return d'

exportSum :: (CPS.Ident, CPS.Sum) -> M ()
exportSum x = do
  xs <- get programSums
  set $ \ s -> s {programSums = x:xs}

convertFun :: (Linear.Ident, Linear.Fun) -> M ()
convertFun (d0, Linear.Fun d1s ty0s ty1 t0) = do
  d0'  <- renameFunIdent d0
  d1s' <- mapM (const gen) d1s
  ty0s' <- mapM convertType ty0s
  d2'  <- gen
  d3'  <- gen
  ty1' <- convertType ty1
  t1'  <- binds d1s d1s' ty0s' $ do
    convertTerm t0 d2' ty1' d3'
  ty2' <- getHandlerType
  exportFun (d0', CPS.Fun (d1s' ++ [d2', d3']) [CPS.ArrowType [ty1', ty2'], ty2'] t1')

exportFun :: (CPS.Ident, CPS.Fun) -> M ()
exportFun x = do
  xs <- get programFuns
  set $ \ s -> s {programFuns = x:xs}

renameFunIdent :: Linear.Ident -> M CPS.Ident
renameFunIdent d = do
  xs <- get funIdentRenames
  case lookup d xs of
    Nothing -> do
      d' <- gen
      set $ \ s -> s {funIdentRenames = (d,d'):xs}
      return d'
    Just d' ->
      return d'

-- d1 is the ident of main
createStartFun :: Linear.Ident -> M CPS.Ident
createStartFun = todo "createStartFun"


createResultSum :: M ()
createResultSum = todo "createResultSum"

data State = S { genInt :: Int
               , programSums :: [(CPS.Ident, CPS.Sum)]
               , programFuns :: [(CPS.Ident, CPS.Fun)]
               , sumIdentRenames :: [(Linear.Ident, CPS.Ident)]
               , funIdentRenames :: [(Linear.Ident, CPS.Ident)]
               , kType :: CPS.Type
               }

run :: Linear.Program -> M CPS.Program -> CPS.Program
run p m = runM m s r k
  where s = S { genInt = 1001
              , programSums = []
              , programFuns = []
              , sumIdentRenames = []
              , funIdentRenames = []
              , kType = CPS.TupleType []
              }
        r = todo "reader"
        k x _ = x

data Reader = R { resultIdent :: CPS.Ident
                , tagTypePairs :: [(Linear.Ident, (Int, (CPS.Type, CPS.Type)))]
                , normalResultIndexes :: [(CPS.Type, Int)]
                , funTypes :: [(Linear.Ident, CPS.Type)]
                , localBindings :: [(Linear.Ident, (CPS.Ident, CPS.Type))]
                }

-- type M a = Maybe a
newtype M a = M { runM :: State -> Reader -> (a -> State -> CPS.Program) -> CPS.Program }

instance Monad M where
  return x = M $ \ s _ k -> k x s
  m >>= f = M $ \ s r k -> runM m s r $ \ x s -> runM (f x) s r k

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
      ty1' <- todo "catch"

      -- we create a new dk which is just a function which creates a constructor and calls the handler.
      -- we create a new handler which calls a top-level function which has the case.
      todo "catch"
    Linear.ReturnTerm d1 -> do
      d1' <- rename d1
      return $ CPS.ApplyTerm dk [d1', dh]
    Linear.ThrowTerm d1 d2 d3 t1 -> do
      d1' <- rename d1
      d2' <- renameTag d2
      d3' <- rename d3
      continue d1 t1 dk dkty $ \ dk ->
        return $ CPS.ApplyTerm dh [d2', dk]
    _ -> todo $ "term: " ++ show t

-- Generates a new ident.
gen :: M CPS.Ident
gen = do
  i <- get genInt
  set (\ s -> s {genInt = i + 1})
  return i


bind :: Linear.Ident -> CPS.Ident -> CPS.Type -> M a -> M a
bind = todo "bind"

binds :: [Linear.Ident] -> [CPS.Ident] -> [CPS.Type] -> M a -> M a
binds [] [] [] m = m
binds (d1:d1s) (d2:d2s) (ty1:ty1s) m = bind d1 d2 ty1 $ binds d1s d2s ty1s m
binds _ _ _ _ = unreachable "binds"

-- | If we are already in tail position, we don't need to create a new
--   delimited continuation. Otherwise, we do.
continue :: Linear.Ident -> Linear.Term -> CPS.Ident -> CPS.Type -> (CPS.Ident -> M CPS.Term) -> M CPS.Term
continue d1 (Linear.ReturnTerm d2) dk dkty f | d1 == d2 = f dk
continue d1 t1 dk dkty f = do
  d1' <- gen
  dh' <- gen
  t1' <- bind d1 d1' (todo "continue") $ do
    convertTerm t1 dk dkty dh'
  dk' <- gen
  t2' <- f dk'
  return $ CPS.LambdaTerm dk' [d1', dh'] [dkty, todo "continue"] t1' t2'

rename :: Linear.Ident -> M CPS.Ident
rename = todo "rename"

renameTag :: Linear.Ident -> M CPS.Ident
renameTag = todo "renameTag"

with :: (Reader -> Reader) -> M a -> M a
with f m = M $ \ s r k -> runM m s (f r) k

get :: (State -> a) -> M a
get f = M $ \ s _ k -> k (f s) s

set :: (State -> State) -> M ()
set f = M $ \ s _ k -> k () (f s)

look :: (Reader -> a) -> M a
look f = M $ \ s r k -> k (f r) s

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: CPS.FromLinear." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: CPS.FromLinear." ++ s
