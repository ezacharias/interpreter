module Compiler.Elaborator where

import           Control.Monad   (liftM)
import           Data.Maybe      (catMaybes)

import qualified Compiler.Lambda as Lambda
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

data Result a where
  Return                 :: a -> Result a
  Bind                   :: Result b -> (b -> Result a) -> Result a
  Gen                    :: Result Int
  LookupUpper            :: String -> Result Lambda.FunctionIdent
  LookupTypeVariable     :: String -> Result Lambda.TypeIdent
  LookupValueVariable    :: String -> Result Lambda.ValueIdent
  LookupConstructorIndex :: String -> Result Lambda.ConstructorIndex

instance Monad Result where
  return = Return
  Return x                 >>= f = f x
  Bind m g                 >>= f = Bind m (\ x -> g x >>= f)
  m                        >>= f = Bind m f

impossible :: a
impossible = error "impossible"

run :: Result Lambda.Program -> Lambda.Program
run m = check genStart m
  where check :: Int -> Result Lambda.Program -> Lambda.Program
        check n (Return x)                          = x
        check n (Bind (Return _) _)                 = error "Compiler.Elaborater.run: unreachable"
        check n (Bind (Bind _ _) _)                 = error "Compiler.Elaborater.run: unreachable"
        check n (Bind Gen k)                        = check (n + 1) (k n)
        check n (Bind (LookupUpper s) k)            = impossible
        check n (Bind (LookupTypeVariable s) k)     = impossible
        check n (Bind (LookupValueVariable s) k)    = impossible
        check n (Bind (LookupConstructorIndex s) k) = impossible

withConstructors :: [(String, Int)] -> Result a -> Result a
withConstructors gs m = check m
  where check (Return x)                          = Return x
        check (Bind (LookupConstructorIndex s) k) = check $ k (maybe (error "withConstructors") id (lookup s gs))
        check (Bind m k)                          = Bind m (check . k)
        check m                                   = check (Bind m Return)

withUppers :: [(String, Int)] -> Result a -> Result a
withUppers gs m = check m
  where check (Return x)               = Return x
        check (Bind (LookupUpper s) k) = check $ k (maybe (error ("withUppers: " ++ s ++ ", " ++ show (map fst gs))) id (lookup s gs))
        check (Bind m k)               = Bind m (check . k)
        check m                        = check (Bind m Return)

withTypes :: [(String, Int)] -> Result a -> Result a
withTypes gs m = check m
  where check (Return x)                      = Return x
        check (Bind (LookupTypeVariable s) k) = check $ k (maybe (error "withTypes") id (lookup s gs))
        check (Bind m k)                      = Bind m (check . k)
        check m                               = check (Bind m Return)

withLower :: String -> Int -> Result a -> Result a
withLower d d' m = check m
  where check (Return x)                       = Return x
        check (Bind (LookupValueVariable s) k)
                                   | s == d    = check $ k d'
                                   | otherwise = Bind (LookupValueVariable s) (check . k)
        check (Bind m k)                       = Bind m (check . k)
        check m                                = check (Bind m Return)

elaborate :: Syntax.Program -> Lambda.Program
elaborate p = run (elaborateProgram p)

funs :: [(Lambda.FunctionIdent, Lambda.Function)]
funs = [ -- Exit
         (0, Lambda.Function [] (Lambda.VariantType 0 [])
               (Lambda.ConstructorTerm 0 [] 0 []))
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
      , ("Unreachable", 9)
      ]

elaborateProgram :: Syntax.Program -> Result Lambda.Program
elaborateProgram (Syntax.Program ds) = do
  (gs1, gs2) <- decEnvs ([], []) ds
  withConstructors (constructorEnv ++ gs1) $ do
    withUppers (env ++ gs2) $ do
      xs1 <- liftM catMaybes $ mapM elaborateVariant ds
      xs2 <- liftM concat $ mapM elaborateFunction ds
      d <- LookupUpper "Main"
      return $ Lambda.Program [] xs1 (funs ++ xs2) d

decEnvs :: ([(String, Int)], [(String, Int)]) -> [Syntax.Dec] -> Result ([(String, Int)], [(String, Int)])
decEnvs (xs, ys) []                               = return (xs, ys)
decEnvs (xs, ys) (Syntax.FunDec _ s _ _ _ _ : ds) = do { d <- Gen; decEnvs (xs, (s, d) : ys) ds }
decEnvs (xs, ys) (Syntax.SumDec _ s _ rs : ds)    = do d <- Gen
                                                       ss <- return $ map (\ (_, s, _) -> s) rs
                                                       ns <- mapM (\ _ -> Gen) rs
                                                       decEnvs (zip ss [0..] ++ xs, zip ss ns ++ ys) ds
decEnvs (xs, ys) (Syntax.TagDec _ s ty : ds)      = do d <- Gen
                                                       decEnvs (xs, (s, d) : ys) ds
decEnvs (xs, ys) (Syntax.NewDec _ s1 "Escape" tys : ds) = do d1 <- Gen
                                                             d2 <- Gen
                                                             ys <- return $ (s1 ++ ".Throw", d1) : ys
                                                             ys <- return $ (s1 ++ ".Catch", d2) : ys
                                                             decEnvs (xs, ys) ds
decEnvs (xs, ys) (Syntax.NewDec _  _ _       _   : _ ) = error "decEnvs new"

elaborateFunction :: Syntax.Dec -> Result [(Lambda.FunctionIdent, Lambda.Function)]
elaborateFunction (Syntax.FunDec _ s ss ps t e) = do
  d  <- LookupUpper s
  ds <- mapM (\ _ -> Gen) ss
  withTypes (zip ss ds) $ do
    e' <- elaborateCurried ps e
    t  <- elaborateType (Syntax.funType ps t)
    return [(d, Lambda.Function ds t e')]
elaborateFunction (Syntax.SumDec _ s1 ss rs) = mapM f (zip [0..] rs)
  where f (i, (_, s2, tys)) = do
          d <- LookupUpper s2
          ds <- mapM (\ _ -> Gen) ss
          withTypes (zip ss ds) $ do
            ty <- elaborateType (Syntax.constructorType tys s1 ss)
            tys' <- mapM (elaborateType . Syntax.typType) tys
            t <- g tys' [] i
            return (d, Lambda.Function ds ty t)
        g []       ds i = return $ Lambda.ConstructorTerm undefined undefined i (map Lambda.VariableTerm ds)
        g (ty:tys) ds i = do d <- Gen
                             t <- g tys (d:ds) i
                             return $ Lambda.LambdaTerm d ty t
elaborateFunction (Syntax.TagDec _ s ty) = do
  d <- LookupUpper s
  ty' <- elaborateType (Syntax.typType ty)
  return $ [(d, Lambda.Function [] ty' (Lambda.TagTerm d))]
elaborateFunction (Syntax.NewDec _ s1 "Escape" [ty1, ty2]) = do d1 <- LookupUpper $ s1 ++ ".Catch"
                                                                d2 <- LookupUpper $ s1 ++ ".Throw"
                                                                d3 <- Gen
                                                                d4 <- Gen
                                                                d5 <- Gen
                                                                d6 <- Gen
                                                                d7 <- Gen
                                                                d8 <- Gen
                                                                d9 <- Gen
                                                                return [ (d1, Lambda.Function [d5] undefined
                                                                                (Lambda.LambdaTerm d6 undefined
                                                                                  (Lambda.LambdaTerm d7 undefined
                                                                                    (Lambda.CatchTerm (Lambda.TagTerm d3)
                                                                                      (Lambda.ApplyTerm (Lambda.VariableTerm d6) Lambda.UnitTerm)
                                                                                      d8 d9
                                                                                      (Lambda.ApplyTerm (Lambda.ApplyTerm (Lambda.VariableTerm d7)
                                                                                                                          (Lambda.VariableTerm d8))
                                                                                                        (Lambda.VariableTerm d9))))))
                                                                       , (d2, Lambda.Function [] undefined
                                                                                (Lambda.LambdaTerm d4 undefined
                                                                                  (Lambda.ThrowTerm (Lambda.TagTerm d3) (Lambda.VariableTerm d4))))
                                                                       ]
elaborateFunction (Syntax.NewDec _ _  _       _         ) = error "elaborateFunction new"

elaborateVariant :: Syntax.Dec -> Result (Maybe (Lambda.VariantIdent, Lambda.Variant))
elaborateVariant (Syntax.FunDec _ _ _ _ _ _) = return Nothing
elaborateVariant (Syntax.SumDec _ s ss rs) = do
  d <- return undefined
  ds <- mapM (\ _ -> Gen) ss
  withTypes (zip ss ds) $ do
    ns <- mapM (\ (_, n, _) -> return n) rs
    xs <- mapM (\ (_, _, tys) -> mapM (elaborateType . Syntax.typType) tys) rs
    return (Just (d, Lambda.Variant ds ns xs))
elaborateVariant (Syntax.TagDec _ _ _) = return Nothing
elaborateVariant (Syntax.NewDec _ _ _ _) = return Nothing

elaborateCurried :: [Syntax.Pat] -> Syntax.Term -> Result Lambda.Term
elaborateCurried [] e     = elaborateTerm e
elaborateCurried (p:ps) e = do
  d <- Gen
  e' <- elaboratePat d p (elaborateCurried ps e)
  t <- elaborateType $ Syntax.patType p
  return $ Lambda.LambdaTerm d t e'

elaboratePat :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term
elaboratePat d p m = elaboratePatAlt d p m (return $ Lambda.Unreachable undefined)

elaboratePats :: [Lambda.ValueIdent] -> [Syntax.Pat] -> Result Lambda.Term -> Result Lambda.Term
elaboratePats ds ps m = elaboratePatsAlt ds ps m (return $ Lambda.Unreachable undefined)

elaboratePatAlt :: Lambda.ValueIdent -> Syntax.Pat -> Result Lambda.Term -> Result Lambda.Term -> Result Lambda.Term
elaboratePatAlt d (Syntax.AscribePat p ty) m1 m2 = elaboratePatAlt d p m1 m2
elaboratePatAlt d (Syntax.LowerPat _ s)    m1 m2 = withLower s d m1
elaboratePatAlt d (Syntax.TuplePat _ ps)   m1 m2 = do ds <- mapM (\ _ -> Gen) ps
                                                      t <- elaboratePatsAlt ds ps m1 m2
                                                      return $ Lambda.UntupleTerm ds (Lambda.VariableTerm d) t
elaboratePatAlt d Syntax.UnderbarPat       m1 m2 = m1
elaboratePatAlt d (Syntax.UnitPat _)       m1 m2 = m1
elaboratePatAlt d (Syntax.UpperPat _ _ _ x ps) m1 m2
                                          = do i <- LookupConstructorIndex x
                                               ds <- mapM (\ _ -> Gen) ps
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
elaborateTerm (Syntax.BindTerm _ p t1 t2)    = do d <- Gen
                                                  t1' <- elaborateTerm t1
                                                  t2' <- elaboratePat d p $ elaborateTerm t2
                                                  return $ Lambda.BindTerm d t1' t2'
elaborateTerm (Syntax.CaseTerm _ t rs)       = do d <- Gen
                                                  t' <- elaborateTerm t
                                                  t2' <- elaborateRules d rs
                                                  return $ Lambda.BindTerm d t' t2'
                                               where elaborateRules d [] = return $ Lambda.Unreachable undefined
                                                     elaborateRules d ((p, t1) : rs) = do
                                                       t2 <- elaborateRules d rs
                                                       d2 <- Gen
                                                       d3 <- Gen
                                                       t1 <- elaboratePatAlt d p (elaborateTerm t1) (return $ Lambda.ApplyTerm (Lambda.VariableTerm d2) Lambda.UnitTerm)
                                                       return $ Lambda.BindTerm d2 (Lambda.LambdaTerm d3 Lambda.UnitType t2) t1

elaborateTerm (Syntax.SeqTerm t1 t2)         = do { d <- Gen; t1' <- elaborateTerm t1; t2' <- elaborateTerm t2; return $ Lambda.BindTerm d t1' t2' }
elaborateTerm (Syntax.TupleTerm pos tys es)  = do { es' <- mapM elaborateTerm es; return $ Lambda.TupleTerm es' }
elaborateTerm (Syntax.UnitTerm pos)          = return Lambda.UnitTerm
elaborateTerm (Syntax.UpperTerm pos tys _ s) = do { d <- LookupUpper s; tys' <- mapM elaborateType tys; return $ Lambda.TypeApplyTerm d tys' }
elaborateTerm (Syntax.VariableTerm pos s)    = do { d <- LookupValueVariable s; return $ Lambda.VariableTerm d }

elaborateType :: Type.Type -> Result Lambda.Type
elaborateType (Type.Arrow t1 t2)    = do { t1' <- elaborateType t1; t2' <- elaborateType t2; return $ Lambda.ArrowType t1' t2' }
elaborateType (Type.Metavariable _) = error "Compiler.Elaborator: all metavariables should have been removed"
elaborateType (Type.Tuple ts)       = do { ts' <- mapM elaborateType ts; return $ Lambda.TupleType ts' }
elaborateType Type.Unit             = return Lambda.UnitType
elaborateType (Type.Variable s)     = liftM Lambda.VariableType (LookupTypeVariable s)
elaborateType (Type.Variant _ _)    = return $ Lambda.VariantType 0 [] -- fix
