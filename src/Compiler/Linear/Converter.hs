-- | Converts a program from Simple to Linear.
module Compiler.Linear.Converter where

import           Data.Maybe      (fromMaybe)

import qualified Compiler.Linear as Linear
import qualified Compiler.Simple as Simple

convert :: Simple.Program -> Linear.Program
convert p = run p $ do
  xs1 <- mapM convertTag (Simple.programTags p)
  xs2 <- mapM convertType (Simple.programRess p)
  xs3 <- mapM convertSum (Simple.programSums p)
  xs4 <- mapM convertFun (Simple.programFuns p)
  d <- renameFun (Simple.programMain p)
  return $ Linear.Program
             { Linear.programTags = xs1
             , Linear.programRess = xs2
             , Linear.programSums = xs3
             , Linear.programFuns = xs4
             , Linear.programMain = d
             }

run :: Simple.Program -> M Linear.Program Linear.Program -> Linear.Program
run p m = runM m k1 k2 s [] 0
  where k1 x k2 = k2 x
        k2 x _ = x
        s = S { tagRenames = zip (map fst (Simple.programTags p)) [0..]
              , sumRenames = zip (map fst (Simple.programSums p)) [0..]
              , funRenames = zip (map fst (Simple.programFuns p)) [0..]
              }

convertTag :: (Simple.Ident, Simple.Tag) -> P (Linear.Ident, Linear.Tag)
convertTag (d1, Simple.Tag ty1 ty2) = do
  d1' <- renameTag d1
  ty1' <- convertType ty1
  ty2' <- convertType ty2
  return (d1', Linear.Tag ty1' ty2')

convertSum :: (Simple.Ident, Simple.Sum) -> P (Linear.Ident, Linear.Sum)
convertSum (d1, Simple.Sum ty1ss) = do
  d1' <- renameSum d1
  ty1ss' <- mapM (mapM convertType) ty1ss
  return (d1', Linear.Sum ty1ss')

convertFun :: (Simple.Ident, Simple.Fun) -> P (Linear.Ident, Linear.Fun)
convertFun (d1, Simple.Fun ty1 t1) = do
  d1' <- renameFun d1
  ty' <- convertType ty1
  t1' <- result $ convertTerm t1
  return (d1', Linear.Fun [] [] ty' t1')

convertTerm :: Simple.Term -> T Simple.Ident
convertTerm (Simple.ApplyTerm t1 t2) = do
  d1' <- convertTerm t1
  d2' <- convertTerm t2
  d3' <- gen
  continue d3' $ \ t3' -> do
    return $ Linear.ApplyTerm d3' d1' d2' t3'
convertTerm (Simple.BindTerm d1 t1 t2) = do
  d1' <- convertTerm t1
  bind d1 d1' $ do
    convertTerm t2
convertTerm (Simple.CaseTerm t1 c1s) = do
  d1' <- convertTerm t1
  c1s' <- mapM convertRule c1s
  d2' <- gen
  continue d2' $ \ t1' -> do
    return $ Linear.CaseTerm d2' d1' c1s' t1'
convertTerm (Simple.CatchTerm d1 _ ty1 t1) = do
  d1' <- renameTag d1
  ty1' <- convertType ty1
  t2' <- result $ convertTerm t1
  d2' <- gen
  continue d2' $ \ t3' -> do
    return $ Linear.CatchTerm d2' d1' ty1' t2' t3'
convertTerm (Simple.ConcatenateTerm t1 t2) = do
  d1' <- convertTerm t1
  d2' <- convertTerm t2
  d3' <- gen
  continue d3' $ \ t3' -> do
    return $ Linear.ConcatenateTerm d3' d1' d2' t3'
convertTerm (Simple.ConstructorTerm d1 i1 t1s) = do
  d1' <- renameSum d1
  d2s' <- convertTerms t1s
  d3' <- gen
  continue d3' $ \ t2' -> do
    return $ Linear.ConstructorTerm d3' d1' i1 d2s' t2'
convertTerm (Simple.FunTerm d1) = do
  d1' <- renameFun d1
  d2' <- gen
  continue d2' $ \ t1' -> do
    return $ Linear.CallTerm d2' d1' [] t1'
convertTerm (Simple.LambdaTerm d1 ty1 t1) = do
  d1' <- gen
  d2' <- gen
  ty1' <- convertType ty1
  t1' <- result $ bind d1 d1' (convertTerm t1)
  continue d2' $ \ t2' -> do
    return $ Linear.LambdaTerm d2' d1' ty1' t1' t2'
convertTerm (Simple.StringTerm x) = do
  d1' <- gen
  continue d1' $ \ t1' -> do
    return $ Linear.StringTerm d1' x t1'
convertTerm (Simple.ThrowTerm d1 t1) = do
  d1' <- renameTag d1
  d2' <- convertTerm t1
  d3' <- gen
  continue d3' $ \ t2' -> do
    return $ Linear.ThrowTerm d3' d1' d2' t2'
convertTerm (Simple.TupleTerm t1s) = do
  d1s' <- convertTerms t1s
  d2' <- gen
  continue d2' $ \ t2' -> do
    return $ Linear.TupleTerm d2' d1s' t2'
convertTerm Simple.UnitTerm = do
  d1' <- gen
  continue d1' $ \ t1' -> do
    return $ Linear.TupleTerm d1' [] t1'
convertTerm (Simple.UnreachableTerm ty) = do
  ty' <- convertType ty
  escape $ Linear.UnreachableTerm ty'
convertTerm (Simple.UntupleTerm d1s t1 t2) = do
  d1s' <- mapM (const gen) d1s
  d2' <- convertTerm t1
  binds d1s d1s' $ do
    adjust (convertTerm t2) (Linear.UntupleTerm d1s' d2')
convertTerm (Simple.VariableTerm d1) = do
  rename d1

convertRule :: ([Simple.Ident], Simple.Term) -> T ([Linear.Ident], Linear.Term)
convertRule (d1s, t1) = do
  d1s' <- mapM (const gen) d1s
  t1' <- result $ binds d1s d1s' (convertTerm t1)
  return (d1s', t1')

convertType :: Simple.Type -> M a Linear.Type
convertType ty =
  case ty of
    Simple.ArrowType ty1 ty2 -> do
      ty1' <- convertType ty1
      ty2' <- convertType ty2
      return $ Linear.ArrowType ty1' ty2'
    Simple.StringType ->
      return $ Linear.StringType
    Simple.TupleType tys -> do
      tys' <- mapM convertType tys
      return $ Linear.TupleType tys'
    Simple.UnitType ->
      return $ Linear.TupleType []
    Simple.SumType d1 -> do
      d1' <- renameSum d1
      return $ Linear.SumType d1'

convertTerms :: [Simple.Term] -> T [Linear.Ident]
convertTerms [] = do
  return []
convertTerms (t:ts) = do
  d <- convertTerm t
  ds <- convertTerms ts
  return $ d:ds

newtype M a b = N { runM :: (b -> (a -> Int -> Linear.Program) -> Int -> Linear.Program)
                         -> (a -> Int -> Linear.Program)
                         -> S
                         -> [(Simple.Ident, Linear.Ident)]
                         -> Int
                         -> Linear.Program }

data S = S
 { tagRenames :: [(Simple.Ident, Linear.Ident)]
 , sumRenames :: [(Simple.Ident, Linear.Ident)]
 , funRenames :: [(Simple.Ident, Linear.Ident)]
 }

type P a = M Linear.Program a

type T a = M Linear.Term a

instance Monad (M a) where
  return x = N $ \ k1 k2 _ _ -> k1 x k2
  m >>= f = N $ \ k1 k2 s r -> runM m (\ x k2 -> runM (f x) k1 k2 s r) k2 s r

gen :: M a Linear.Ident
gen = N $ \ k1 k2 _ _ n -> k1 n k2 (n + 1)

getState :: M a S
getState = N $ \ k1 k2 s _ -> k1 s k2

renameTag :: Simple.Ident -> M a Linear.Ident
renameTag d = do
  s <- getState
  return $ fromMaybe (unreachable "renameTag") (lookup d (tagRenames s))

renameFun :: Simple.Ident -> M a Linear.Ident
renameFun d = do
  s <- getState
  return $ fromMaybe (unreachable "renameFun") (lookup d (funRenames s))

renameSum :: Simple.Ident -> M a Linear.Ident
renameSum d = do
  s <- getState
  return $ fromMaybe (unreachable "renameSum") (lookup d (sumRenames s))

getRenames :: M a [(Simple.Ident, Linear.Ident)]
getRenames = N $ \ k1 k2 _ r -> k1 r k2

rename :: Simple.Ident -> M a Linear.Ident
rename d = do
  r <- getRenames
  return $ fromMaybe (unreachable "rename") (lookup d r)

bind :: Simple.Ident -> Linear.Ident -> M a b -> M a b
bind d1 d2 m = N $ \ k1 k2 s r -> runM m k1 k2 s ((d1,d2):r)

binds :: [Simple.Ident] -> [Linear.Ident] -> M a b -> M a b
binds [] [] m = m
binds (d1:d1s) (d2:d2s) m = bind d1 d2 $ binds d1s d2s m
binds _ _ _ = unreachable "binds"

continue :: Linear.Ident -> (Linear.Term -> T Linear.Term) -> T Linear.Ident
continue d f = N $ \ k1 k2 s r -> k1 d (\ t -> runM (f t) (\ t k2 -> k2 t) k2 s r)

adjust :: T Linear.Ident -> (Linear.Term -> Linear.Term) -> T Linear.Ident
adjust m f = N $ \ k1 k2 -> runM m k1 (\ t -> k2 (f t))

escape :: Linear.Term -> T Linear.Ident
escape t = N $ \ k1 k2 _ _ -> k2 t

result :: T Simple.Ident -> M a Linear.Term
result m = N $ \ k1 k2 -> runM m (\ d1 k2 -> k2 (Linear.ReturnTerm d1)) (\ t1 -> k1 t1 k2)

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Linear.Converter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Linear.Converter." ++ s
