module Compiler.Elaborator where

import           Data.Maybe      (fromJust)

import qualified Compiler.Lambda as Lambda
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

data Result a = Normal a
              | Gen (Int -> Result a)
              | LookupUpper String (Lambda.FunctionIdent -> Result a)
              | LookupTypeVariable String (Lambda.TypeIdent -> Result a)
              | LookupValueVariable String (Lambda.ValueIdent -> Result a)

instance Monad Result where
  return = Normal
  Normal x                >>= f = f x
  Gen k                   >>= f = Gen (\ x -> k x >>= f)
  LookupUpper s k         >>= f = LookupUpper s (\ x -> k x >>= f)
  LookupTypeVariable s k  >>= f = LookupTypeVariable s (\ x -> k x >>= f)
  LookupValueVariable s k >>= f = LookupValueVariable s (\ x -> k x >>= f)

impossible :: a
impossible = error "impossible"

run :: Result a -> a
run m = check 1 m
  where check n (Normal x)                = x
        check n (Gen k)                   = check (n + 1) (k n)
        check n (LookupUpper s k)         = impossible
        check n (LookupTypeVariable s k)  = impossible
        check n (LookupValueVariable s k) = impossible

gen :: a -> Result Int
gen _ = Gen Normal

withUppers :: [(String, Int)] -> Result a -> Result a
withUppers gs m = check m
  where check (Normal x)                = Normal x
        check (Gen k)                   = Gen (check . k)
        check (LookupUpper s k)         = check $ k (lookupJust s gs)
        check (LookupTypeVariable s k)  = LookupTypeVariable s (check . k)
        check (LookupValueVariable s k) = LookupValueVariable s (check . k)

withTypes :: [(String, Int)] -> Result a -> Result a
withTypes gs m = check m
  where check (Normal x)                = Normal x
        check (Gen k)                   = Gen (check . k)
        check (LookupUpper s k)         = LookupUpper s (check . k)
        check (LookupTypeVariable s k)  = check $ k (lookupJust s gs)
        check (LookupValueVariable s k) = LookupValueVariable s (check . k)

-- data Program = Program [(TagIdent, Tag)] [(VariantIdent, Variant)] [(FunctionIdent, Function)] FunctionIdent

elaborate :: Syntax.Program -> Lambda.Program
elaborate p = run (elaborateProgram p)

funs :: [(Lambda.FunctionIdent, Lambda.Function)]
funs = [(0, Lambda.Function [] (Lambda.VariantType 0 [])
              (Lambda.ConstructorTerm 0 [] 0 []))]

env :: [(String, Int)]
env = [("Exit", 0)]

elaborateProgram :: Syntax.Program -> Result Lambda.Program
elaborateProgram (Syntax.Program ds) = do gs <- mapM f ds
                                          withUppers (env ++ gs) $ do
                                            xs <- mapM elaborateFunction ds
                                            d <- LookupUpper "Main" Normal
                                            return $ Lambda.Program [] [] (funs ++ xs) d
  where f (Syntax.FunDec _ s _ _ _ _) = do { d <- gen (); return (s, d) }

elaborateFunction :: Syntax.Dec -> Result (Lambda.FunctionIdent, Lambda.Function)
elaborateFunction (Syntax.FunDec _ s ss ps t e) = do d  <- LookupUpper s Normal
                                                     ds <- mapM gen ss
                                                     withTypes (zip ss ds) $ do
                                                       e' <- elaborateCurried ps e
                                                       t  <- elaborateType (Syntax.funType ps t)
                                                       return (d, Lambda.Function ds t e')

elaborateCurried :: [Syntax.Pat] -> Syntax.Term -> Result Lambda.Term
elaborateCurried [] e     = elaborateTerm e
elaborateCurried (p:ps) e = do d <- Gen Normal
                               e' <- elaboratePat d p (elaborateCurried ps e)
                               t <- elaborateType $ Syntax.patType p
                               return $ Lambda.LambdaTerm d t e'

elaboratePat :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term
elaboratePat d (Syntax.UnitPat _) m = m

elaborateTerm :: Syntax.Term -> Result Lambda.Term
elaborateTerm (Syntax.ApplyTerm _ t1 t2)     = do { t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.ApplyTerm t1' t2' }
elaborateTerm (Syntax.TupleTerm pos tys es)  = do { es' <- mapM elaborateTerm es; return $ Lambda.TupleTerm es' }
elaborateTerm (Syntax.UnitTerm pos)          = return Lambda.UnitTerm
elaborateTerm (Syntax.UpperTerm pos tys _ s) = do { d <- LookupUpper s Normal; tys' <- mapM elaborateType tys; return $ Lambda.TypeApplyTerm d tys' }
elaborateTerm (Syntax.VariableTerm pos s)    = do { d <- LookupValueVariable s Normal; return $ Lambda.VariableTerm d }

elaborateType :: Type.Type -> Result Lambda.Type
elaborateType (Type.Arrow t1 t2)    = do { t1' <- elaborateType t1; t2' <- elaborateType t2; return $ Lambda.ArrowType t1' t2' }
elaborateType (Type.Metavariable _) = error "Compiler.Elaborator: all metavariables should have been removed"
elaborateType (Type.Tuple ts)       = do { ts' <- mapM elaborateType ts; return $ Lambda.TupleType ts' }
elaborateType Type.Unit             = return Lambda.UnitType
elaborateType (Type.Variable s)     = LookupTypeVariable s (Normal . Lambda.VariableType)
elaborateType (Type.Variant _ _)    = return $ Lambda.VariantType 0 [] -- fix

-- Utility

lookupJust :: Eq a => a -> [(a, b)] -> b
lookupJust key = fromJust . lookup key
