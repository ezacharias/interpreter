module Compiler.Elaborator where

import           Control.Monad   (liftM)
import           Data.Maybe      (catMaybes, fromJust)

import qualified Compiler.Lambda as Lambda
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

data Result a = Normal a
              | Gen (Int -> Result a)
              | LookupUpper String (Lambda.FunctionIdent -> Result a)
              | LookupTypeVariable String (Lambda.TypeIdent -> Result a)
              | LookupValueVariable String (Lambda.ValueIdent -> Result a)
              | LookupConstructorIndex String (Lambda.ConstructorIndex -> Result a)

instance Monad Result where
  return = Normal
  Normal x                   >>= f = f x
  Gen k                      >>= f = Gen (\ x -> k x >>= f)
  LookupUpper s k            >>= f = LookupUpper s (\ x -> k x >>= f)
  LookupConstructorIndex s k >>= f = LookupConstructorIndex s (\x -> k x >>= f)
  LookupTypeVariable s k     >>= f = LookupTypeVariable s (\ x -> k x >>= f)
  LookupValueVariable s k    >>= f = LookupValueVariable s (\ x -> k x >>= f)

impossible :: a
impossible = error "impossible"

run :: Result a -> a
run m = check genStart m
  where check n (Normal x)                   = x
        check n (Gen k)                      = check (n + 1) (k n)
        check n (LookupUpper s k)            = impossible
        check n (LookupTypeVariable s k)     = impossible
        check n (LookupValueVariable s k)    = impossible
        check n (LookupConstructorIndex s k) = impossible

gen :: a -> Result Int
gen _ = Gen Normal

withConstructors :: [(String, Int)] -> Result a -> Result a
withConstructors gs m = check m
  where check (Normal x)                   = Normal x
        check (Gen k)                      = Gen (check . k)
        check (LookupUpper s k)            = LookupUpper s (check . k)
        check (LookupConstructorIndex s k) = check $ k (lookupJust s gs)
        check (LookupTypeVariable s k)     = LookupTypeVariable s (check . k)
        check (LookupValueVariable s k)    = LookupValueVariable s (check . k)

withUppers :: [(String, Int)] -> Result a -> Result a
withUppers gs m = check m
  where check (Normal x)                   = Normal x
        check (Gen k)                      = Gen (check . k)
        check (LookupUpper s k)            = check $ k (lookupJust s gs)
        check (LookupConstructorIndex s k) = LookupConstructorIndex s (check . k)
        check (LookupTypeVariable s k)     = LookupTypeVariable s (check . k)
        check (LookupValueVariable s k)    = LookupValueVariable s (check . k)

withTypes :: [(String, Int)] -> Result a -> Result a
withTypes gs m = check m
  where check (Normal x)                   = Normal x
        check (Gen k)                      = Gen (check . k)
        check (LookupUpper s k)            = LookupUpper s (check . k)
        check (LookupConstructorIndex s k) = LookupConstructorIndex s (check . k)
        check (LookupTypeVariable s k)     = check $ k (lookupJust s gs)
        check (LookupValueVariable s k)    = LookupValueVariable s (check . k)

withLower :: String -> Int -> Result a -> Result a
withLower d d' m = check m
  where check (Normal x)                   = Normal x
        check (Gen k)                      = Gen (check . k)
        check (LookupUpper s k)            = LookupUpper s (check . k)
        check (LookupConstructorIndex s k) = LookupConstructorIndex s (check . k)
        check (LookupTypeVariable s k)     = LookupTypeVariable s (check . k)
        check (LookupValueVariable s k)
                               | s == d    = check $ k d'
                               | otherwise = LookupValueVariable s (check . k)

elaborate :: Syntax.Program -> Lambda.Program
elaborate p = run (elaborateProgram p)

funs :: [(Lambda.FunctionIdent, Lambda.Function)]
funs = [ -- Exit
         (0, Lambda.Function [] (Lambda.VariantType 0 [])
               (Lambda.ConstructorTerm 0 [] 0 []))
         -- Handle
       , (1, Lambda.Function [] undefined
               (Lambda.LambdaTerm 2 undefined
                 (Lambda.LambdaTerm 3 undefined
                   (Lambda.UntupleTerm [4, 5] (Lambda.VariableTerm 2)
                     (Lambda.CatchTerm (Lambda.VariableTerm 4)
                                       (Lambda.ApplyTerm (Lambda.VariableTerm 5) Lambda.UnitTerm)
                                       6
                                       7
                                       (Lambda.ApplyTerm (Lambda.ApplyTerm (Lambda.VariableTerm 3) (Lambda.VariableTerm 6))
                                                         (Lambda.VariableTerm 7)))))))
         -- Throw
       , (6, Lambda.Function [] undefined
               (Lambda.LambdaTerm 7 undefined
                 (Lambda.LambdaTerm 8 undefined
                   (Lambda.ThrowTerm (Lambda.VariableTerm 7) (Lambda.VariableTerm 8)))))
         -- Unreachable
       , (9, Lambda.Function [10] (Lambda.VariableType 10)
               (Lambda.Unreachable (Lambda.VariableType 10)))
       ]

genStart :: Int
genStart = 11

constructorEnv :: [(String, Int)]
constructorEnv = [ ("Exit", 0)
                 ]

env :: [(String, Int)]
env = [ ("Exit", 0)
      , ("Handle", 1)
      , ("Throw", 6)
      , ("Unreachable", 9)
      ]

elaborateProgram :: Syntax.Program -> Result Lambda.Program
elaborateProgram (Syntax.Program ds) = do
  (gs1, gs2) <- decEnvs ([], []) ds
  withConstructors (constructorEnv ++ gs1) $ do
    withUppers (env ++ gs2) $ do
      xs1 <- liftM catMaybes $ mapM elaborateVariant ds
      xs2 <- liftM concat $ mapM elaborateFunction ds
      d <- LookupUpper "Main" Normal
      return $ Lambda.Program [] xs1 (funs ++ xs2) d

decEnvs :: ([(String, Int)], [(String, Int)]) -> [Syntax.Dec] -> Result ([(String, Int)], [(String, Int)])
decEnvs (xs, ys) []                               = return (xs, ys)
decEnvs (xs, ys) (Syntax.FunDec _ s _ _ _ _ : ds) = do { d <- gen (); decEnvs (xs, (s, d) : ys) ds }
decEnvs (xs, ys) (Syntax.SumDec _ s _ rs : ds)    = do d <- gen ()
                                                       ss <- return $ map (\ (_, s, _) -> s) rs
                                                       ns <- mapM gen rs
                                                       decEnvs (zip ss [0..] ++ xs, zip ss ns ++ ys) ds
decEnvs (xs, ys) (Syntax.TagDec _ s ty : ds)      = do d <- gen ()
                                                       decEnvs (xs, (s, d) : ys) ds

elaborateFunction :: Syntax.Dec -> Result [(Lambda.FunctionIdent, Lambda.Function)]
elaborateFunction (Syntax.FunDec _ s ss ps t e) = do
  d  <- LookupUpper s Normal
  ds <- mapM gen ss
  withTypes (zip ss ds) $ do
    e' <- elaborateCurried ps e
    t  <- elaborateType (Syntax.funType ps t)
    return [(d, Lambda.Function ds t e')]
elaborateFunction (Syntax.SumDec _ s1 ss rs) = mapM f (zip [0..] rs)
  where f (i, (_, s2, tys)) = do
          d <- LookupUpper s2 Normal
          ds <- mapM gen ss
          withTypes (zip ss ds) $ do
            ty <- elaborateType (Syntax.constructorType tys s1 ss)
            tys' <- mapM (elaborateType . Syntax.typType) tys
            t <- g tys' [] i
            return (d, Lambda.Function ds ty t)
        g []       ds i = return $ Lambda.ConstructorTerm undefined undefined i (map Lambda.VariableTerm ds)
        g (ty:tys) ds i = do d <- gen ()
                             t <- g tys (d:ds) i
                             return $ Lambda.LambdaTerm d ty t
elaborateFunction (Syntax.TagDec _ s ty) = do
  d <- LookupUpper s Normal
  ty' <- elaborateType (Syntax.typType ty)
  return $ [(d, Lambda.Function [] ty' (Lambda.TagTerm d))]

elaborateVariant :: Syntax.Dec -> Result (Maybe (Lambda.VariantIdent, Lambda.Variant))
elaborateVariant (Syntax.FunDec _ _ _ _ _ _) = return Nothing
elaborateVariant (Syntax.SumDec _ s ss rs) = do
  d <- return undefined
  ds <- mapM gen ss
  withTypes (zip ss ds) $ do
    ns <- mapM (\ (_, n, _) -> return n) rs
    xs <- mapM (\ (_, _, tys) -> mapM (elaborateType . Syntax.typType) tys) rs
    return (Just (d, Lambda.Variant ds ns xs))
elaborateVariant (Syntax.TagDec _ _ _) = return Nothing

elaborateCurried :: [Syntax.Pat] -> Syntax.Term -> Result Lambda.Term
elaborateCurried [] e     = elaborateTerm e
elaborateCurried (p:ps) e = do
  d <- Gen Normal
  e' <- elaboratePat d p (elaborateCurried ps e)
  t <- elaborateType $ Syntax.patType p
  return $ Lambda.LambdaTerm d t e'

elaboratePat :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term
elaboratePat d p m = elaboratePatAlt d p m (return $ Lambda.Unreachable undefined)

elaboratePats :: [Lambda.ValueIdent] -> [Syntax.Pat] -> Result Lambda.Term -> Result Lambda.Term
elaboratePats ds ps m = elaboratePatsAlt ds ps m (return $ Lambda.Unreachable undefined)

elaboratePatAlt :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term -> Result Lambda.Term
elaboratePatAlt d (Syntax.AscribePat p ty) m1 m2 = elaboratePatAlt d p m1 m2
elaboratePatAlt d (Syntax.LowerPat s)      m1 m2 = withLower s d m1
elaboratePatAlt d (Syntax.TuplePat _ ps)   m1 m2 = do ds <- mapM gen ps
                                                      t <- elaboratePatsAlt ds ps m1 m2
                                                      return $ Lambda.UntupleTerm ds (Lambda.VariableTerm d) t
elaboratePatAlt d Syntax.UnderbarPat       m1 m2 = m1
elaboratePatAlt d (Syntax.UnitPat _)       m1 m2 = m1
elaboratePatAlt d (Syntax.UpperPat _ _ _ x ps) m1 m2
                                          = do i <- LookupConstructorIndex x Normal
                                               ds <- mapM gen ps
                                               m1' <- elaboratePatsAlt ds ps m1 m2
                                               m2' <- m2
                                               return $ Lambda.TestTerm (Lambda.VariableTerm d) i ds m1' m2'

elaboratePatsAlt :: [Lambda.ValueIdent] -> [Syntax.Pat] -> Result Lambda.Term -> Result Lambda.Term -> Result Lambda.Term
elaboratePatsAlt []     []     m1 m2 = m1
elaboratePatsAlt (d:ds) (p:ps) m1 m2 = elaboratePatAlt d p (elaboratePats ds ps m1) m2
elaboratePatsAlt _      _      m1 m2 = impossible

elaborateTerm :: Syntax.Term -> Result Lambda.Term
elaborateTerm (Syntax.ApplyTerm _ t1 t2)     = do { t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.ApplyTerm t1' t2' }
elaborateTerm (Syntax.AscribeTerm _ t _)     = elaborateTerm t
elaborateTerm (Syntax.BindTerm _ p t1 t2)    = do d <- gen ()
                                                  t1' <- elaborateTerm t1
                                                  t2' <- elaboratePat d p $ elaborateTerm t2
                                                  return $ Lambda.BindTerm d t1' t2'
elaborateTerm (Syntax.CaseTerm _ t rs)       = do d <- gen ()
                                                  t' <- elaborateTerm t
                                                  t2' <- elaborateRules d rs
                                                  return $ Lambda.BindTerm d t' t2'
                                               where elaborateRules d [] = return $ Lambda.Unreachable undefined
                                                     elaborateRules d ((p, t1) : rs) = do
                                                       t2 <- elaborateRules d rs
                                                       d2 <- gen ()
                                                       d3 <- gen ()
                                                       t1 <- elaboratePatAlt d p (elaborateTerm t1) (return $ Lambda.ApplyTerm (Lambda.VariableTerm d2) Lambda.UnitTerm)
                                                       return $ Lambda.BindTerm d2 (Lambda.LambdaTerm d3 Lambda.UnitType t2) t1

elaborateTerm (Syntax.SeqTerm t1 t2)         = do { d <- gen (); t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.BindTerm d t1' t2' }
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
