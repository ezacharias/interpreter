-- Lambda lifting.

module Compiler.Direct.Converter where

import           Control.Monad       (forM)

import qualified Compiler.CPS        as CPS
import qualified Compiler.Direct     as Direct

convert :: CPS.Program -> Direct.Program
convert p = run p $ do
  mapM_ convertSum (CPS.programSums p)
  mapM_ convertFun (CPS.programFuns p)
  finish
  x1s <- get exportedSums
  x2s <- todo "convert"
  d <- renameFunIdent (CPS.programStart p)
  return $ Direct.Program x1s x2s d

-- Not sure yet.
convertSum :: (CPS.Ident, CPS.Sum) -> M ()
convertSum (d, CPS.Sum tyss) = do
  d' <- renameSumIdent d
  tyss' <- mapM (mapM convertType) tyss
  exportSum (d', Direct.Sum tyss')

convertFun :: (CPS.Ident, CPS.Fun) -> M ()
convertFun (d0, CPS.Fun d1s ty1s t1) = do
  d0'  <- renameFunIdent d0
  d1s'  <- mapM (const gen) d1s
  ty1s' <- mapM convertType ty1s
  t1' <- binds d1s d1s' ty1s' $
           convertTerm t1
  exportFun (d0', Direct.Fun d1s' ty1s' t1')

-- We now have the completed variant types, so we can generate them and the
-- apply functions.
finish :: M ()
finish = todo "finish"

renameSumIdent :: CPS.Ident -> M Direct.Ident
renameSumIdent d = do
  xs <- get sumIdents
  case lookup d xs of
    Just d' ->
      return d'
    Nothing -> do
      d' <- gen
      modify $ \ s -> s {sumIdents = (d,d'):xs}
      return d'

renameFunIdent :: CPS.Ident -> M Direct.Ident
renameFunIdent d = do
  xs <- get funIdents
  case lookup d xs of
    Just d' ->
      return d'
    Nothing -> do
      d' <- gen
      modify $ \ s -> s {funIdents = (d,d'):xs}
      return d'

run :: CPS.Program -> M Direct.Program -> Direct.Program
run p m = runM m k s
 where k x _ = x
       s = S { genInt = 0
             , sumIdents = []
             , funIdents = []
             , arrowSumIdents = []
             , exportedSums = []
             }

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
      ty2' <- getType d2'
      bind d1 d2' ty2' $ do
        convertTerm t1
    CPS.ConcatenateTerm d1 d2 d3 t1 -> do
      d1' <- gen
      d2' <- renameIdent d2
      d3' <- renameIdent d3
      t1' <- bind d1 d1' Direct.StringType $ do
               convertTerm t1
      return $ Direct.ConcatenateTerm d1' d2' d3' t1'
    CPS.ExitTerm ->
      return Direct.ExitTerm
    CPS.LambdaTerm d1 d2s ty2s t1 t2 -> do
      ty2s' <- mapM convertType ty2s
      d3' <- getArrowSumIdent ty2s'
      d1' <- gen
      ty1' <- return $ Direct.SumType d3'
      (i, d4s') <- resetFree $ do
                     d2s' <- mapM (const gen) d2s
                     t1' <- binds d2s d2s' ty2s' $ do
                              convertTerm t1
                     d4s' <- free
                     ty4s' <- mapM getType d4s'
                     d5' <- getFunIdent ty4s' ty2s'
                     -- return (d4s', ty4s', t1')
                     exportFun (d5', Direct.Fun (d4s' ++ d2s') (ty4s' ++ ty2s') t1')
                     i <- addConstructor d3' d4s'
                     return (i, d4s')
      t2' <- bind d1 d1' ty1' $ do
               convertTerm t2
      return $ Direct.ConstructorTerm d1' d3' i d4s' t2'
    _ ->
      todo "convertTerm"

-- This takes:
--   d0      the name of the function to generate
--   sd      the ident of the sum type
--   ty2s    the types of the arguments to the closure
--   xs      the types of the free vars paired with the ident of the direct
--           function to call
createApplyFun :: Direct.Ident -> Direct.Ident -> [Direct.Type] -> [([Direct.Type], Direct.Ident)] -> M ()
createApplyFun d0 sd ty2s xs = do
  ty1 <- return $ Direct.SumType sd
  d1 <- genLocal ty1
  d2s <- mapM genLocal ty2s
  cs <- forM xs $ \ (ty3s, d4) -> do
          d3s <- mapM genLocal ty3s
          return $ (d3s, Direct.CallTerm d4 (d3s ++ d2s))
  exportFun (d0, Direct.Fun (d1:d2s) (ty1:ty2s) (Direct.CaseTerm d1 cs))

addConstructor :: Direct.Ident -> [Direct.Ident] -> M Int
addConstructor = todo "addConstructor"

-- The first is the free variables and the second is the arguments.
getFunIdent :: [Direct.Type] -> [Direct.Type] -> M Direct.Ident
getFunIdent = todo "getFunIdent"

exportSum :: (Direct.Ident, Direct.Sum) -> M ()
exportSum x = do
  modify $ \ s -> s {exportedSums = x : exportedSums s}

exportFun :: (Direct.Ident, Direct.Fun) -> M ()
exportFun = todo "exportFun"

convertType :: CPS.Type -> M Direct.Type
convertType ty =
  case ty of
    CPS.ArrowType tys -> do
      tys' <- mapM convertType tys
      d' <- getArrowSumIdent tys'
      return $ Direct.SumType d'
    CPS.StringType ->
      return Direct.StringType
    CPS.TupleType tys -> do
      tys' <- mapM convertType tys
      return $ Direct.TupleType tys'
    CPS.SumType d -> do
      d' <- renameSumIdent d
      return $ Direct.SumType d'

-- Returning from a bind must remove the ident from the use list.
bind :: CPS.Ident -> Direct.Ident -> Direct.Type -> M a -> M a
bind = todo "bind"

binds :: [CPS.Ident] -> [Direct.Ident] -> [Direct.Type] -> M a -> M a
binds [] [] [] m = m
binds (d:ds) (d':ds') (ty':tys') m = bind d d' ty' $ binds ds ds' tys' m
binds _ _ _ _ = unreachable "binds"

-- Renaming must mark the ident as used.
renameIdent :: CPS.Ident -> M Direct.Ident
renameIdent = todo "renameIdent"

genLocal :: Direct.Type -> M Direct.Ident
genLocal ty = do
  d <- gen
  todo "genLocal"

gen :: M Direct.Ident
gen = do
  i <- get genInt
  modify $ \ s -> s {genInt = i + 1}
  return i

getType :: Direct.Ident -> M Direct.Type
getType = todo "getType"

-- Uses the ident of the variant type for the closure.
getApplyFun :: Direct.Ident -> M Direct.Ident
getApplyFun = todo "getApplyFun"

-- Arrow types are converted into sums. This generates the sum idents.
getArrowSumIdent :: [Direct.Type] -> M Direct.Ident
getArrowSumIdent tys = do
  xs <- get arrowSumIdents
  case lookup tys xs of
    Just d ->
      return d
    Nothing -> do
      d <- gen
      modify $ \ s -> s {arrowSumIdents = (tys,d):xs}
      return d

-- This is a tricky function. It must reset the free variable list.
-- Importantly, it must ensure the renames in the body are different from the
-- renames outside.
resetFree :: M a -> M a
resetFree = todo "resetFree"
  -- xs <- free
  -- setfree []
  -- z <- m
  -- ys <- free
  -- setfree xs ++ ys
  -- return z

free :: M [Direct.Ident]
free = todo "free"

newtype M a = M { runM :: (a -> State -> Direct.Program) -> State -> Direct.Program }

instance Monad M where
  return x = M (\ k -> k x)
  m >>= f = M (\ k -> runM m (\ x -> runM (f x) k))

data State = S
 { genInt :: Int
 , sumIdents :: [(CPS.Ident, Direct.Ident)]
 , funIdents :: [(CPS.Ident, Direct.Ident)]
 , arrowSumIdents :: [([Direct.Type], Direct.Ident)]
 , exportedSums :: [(Direct.Ident, Direct.Sum)]
 }

get :: (State -> a) -> M a
get f =  M (\ k s -> k (f s) s)

modify :: (State -> State) -> M ()
modify f = M (\ k s -> k () (f s))

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Direct.Converter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Direct.Converter." ++ s
