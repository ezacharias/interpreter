module Compiler.Meta where

-- import Control.Monad (liftM)
-- import           Data.Maybe      (fromJust)

import           Compiler.Syntax
import qualified Compiler.Type   as Type


addMetavariables :: Program -> Program
addMetavariables p = convertProgram (gatherProgram p) p


--------------------------------------------------------------------------------
-- Gather the top-level types.
--------------------------------------------------------------------------------

data Env = Env
             { envUnits        :: [(String, ([String], Env))]
             , envModules      :: [(String, Env)]
             , envFunctions    :: [(String, ([String], Type.Type))]
             , envConstructors :: [(String, ([String], [Type.Type], Type.Type))]
             }

emptyEnv :: Env
emptyEnv = Env [] [] [] []

builtinEnv :: Env
builtinEnv = Env [ ( "Escape"
                   , ( ["a", "b"]
                     , Env []
                           []
                           [ ( "Throw"
                             , ( []
                               , Type.Arrow (Type.Variable "a") (Type.Variable "b")
                               )
                             )
                           , ( "Catch"
                             , ( ["c"]
                               , Type.Arrow (Type.Arrow Type.Unit
                                                        (Type.Variable "c"))
                                            (Type.Arrow (Type.Arrow (Type.Variable "a")
                                                                    (Type.Arrow (Type.Arrow (Type.Variable "b")
                                                                                            (Type.Variable "c"))
                                                                                (Type.Variable "c")))
                                                        (Type.Variable "c"))
                               )
                             )
                           ]
                           []
                     )
                   )
                 ]
                 []
                 [ ( "Exit"
                   , ([], Type.Variant ["Output"] [])
                   )
                 ]
                 []

envWithUnit :: Env -> String -> ([String], Env) -> Env
envWithUnit (Env x1s x2s x3s x4s) s x = Env ((s,x):x1s) x2s x3s x4s

envWithModule :: Env -> String -> Env -> Env
envWithModule (Env x1s x2s x3s x4s) s x = Env x1s ((s,x):x2s) x3s x4s

envWithFunction :: Env -> String -> ([String], Type.Type) -> Env
envWithFunction (Env x1s x2s x3s x4s) s x = Env x1s x2s ((s,x):x3s) x4s

envWithConstructor :: Env -> String -> ([String], [Type.Type], Type.Type) -> Env
envWithConstructor (Env x1s x2s x3s x4s) s x = Env x1s x2s x3s ((s,x):x4s)

envStackLookupUnit :: [Env] -> [String] -> ([String], Env)
envStackLookupUnit [] q = error $ "envStackLookupUnit: " ++ show q
envStackLookupUnit (r:rs) q = maybe failure id (envLookupUnit r q)
  where failure = envStackLookupUnit rs q

envLookupUnit :: Env -> [String] -> Maybe ([String], Env)
envLookupUnit r []    = error "envLookupUnit"
envLookupUnit r [s]   = lookup s (envUnits r)
envLookupUnit r (s:q) = do r <- lookup s (envModules r)
                           envLookupUnit r q


gatherProgram :: Program -> Env
gatherProgram (Program ds) = foldl (gatherDec [] []) builtinEnv ds

gatherDec :: [String] -> [Env] -> Env -> Dec -> Env
gatherDec l rs r (FunDec _ s ss ps ty _) = envWithFunction r s (ss, funType ps ty)
gatherDec l rs r (ModDec _ s ds)         = envWithModule r s $ foldl (gatherDec (s:l) (r:rs)) emptyEnv ds
gatherDec l rs r (NewDec _ s q tys)      = envWithModule r s $ unitApply q (s:l) (envStackLookupUnit (r:rs) q) (map convertType tys)
gatherDec l rs r (SumDec _ s ss cs)      = foldl (gatherConstructor (s:l) ss) r cs
gatherDec l rs r (UnitDec _ s ss ds)     = envWithUnit r s $ (ss, foldl (gatherDec (s:l) (r:rs)) emptyEnv ds)

gatherConstructor :: [String] -> [String] -> Env -> (Pos, String, [Typ]) -> Env
gatherConstructor q ss r (_, s, tys) =
  let r' = envWithFunction r s (ss, constructorType tys q ss)
      r'' = envWithConstructor r' s (ss, map typType tys, Type.Variant q (map Type.Variable ss))
   in r''

unitApply :: [String] -> [String] -> ([String], Env) -> [Type.Type] -> Env
unitApply q1 q2 (ss, r) tys = envSubstitute q1 q2 (zip ss tys) r

envSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> Env -> Env
envSubstitute q1 q2 ps (Env x1s x2s x3s x4s) = Env (map (unitSubstitute q1 q2 ps) x1s)
                                                   (map (modSubstitute q1 q2 ps) x2s)
                                                   (map (funSubstitute q1 q2 ps) x3s)
                                                   (map (conSubstitute q1 q2 ps) x4s)

modSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, Env) -> (String, Env)
modSubstitute q1 q2 ps (s, r) = (s, envSubstitute q1 q2 ps r)

unitSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, ([String], Env)) -> (String, ([String], Env))
unitSubstitute q1 q2 ps (s, (ss, r)) = (s, (ss, envSubstitute q1 q2 ps' r))
  where ps' = filter (\ (s2, _) -> not (elem s2 ss)) ps

funSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, ([String], Type.Type)) -> (String, ([String], Type.Type))
funSubstitute q1 q2 ps (s, (ss, ty)) = (s, (ss, typeSubstitute q1 q2 ps' ty))
  where ps' = filter (\ (s2, _) -> not (elem s2 ss)) ps

conSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, ([String], [Type.Type], Type.Type)) -> (String, ([String], [Type.Type], Type.Type))
conSubstitute = error "cs"

typeSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> Type.Type -> Type.Type
typeSubstitute q1 q2 ps (Type.Arrow ty1 ty2)  = Type.Arrow (typeSubstitute q1 q2 ps ty1) (typeSubstitute q1 q2 ps ty2)
typeSubstitute q1 q2 ps (Type.Metavariable i) = Type.Metavariable i
typeSubstitute q1 q2 ps (Type.Tuple tys)      = Type.Tuple (map (typeSubstitute q1 q2 ps) tys)
typeSubstitute q1 q2 ps Type.Unit             = Type.Unit
typeSubstitute q1 q2 ps (Type.Variable s)     = maybe (Type.Variable s) id (lookup s ps)
typeSubstitute q1 q2 ps (Type.Variant q tys)  = Type.Variant (maybe q id (f q1 q)) (map (typeSubstitute q1 q2 ps) tys)
  where f (s1:q1) (s:q) | s1 == s   = f q1 q
                        | otherwise = Nothing
        f []      q                 = Just $ q2 ++ q
        f q1      []                = Nothing



--------------------------------------------------------------------------------
-- Use the top level types to add type information.
--------------------------------------------------------------------------------

envStackLookupMod :: [Env] -> String -> Env
envStackLookupMod rs s = error "eslm"

convertProgram :: Env -> Program -> Program
convertProgram r (Program ds) = Program (map (convertDec [r]) ds)

convertDec :: [Env] -> Dec -> Dec
convertDec rs (UnitDec pos s ss ds)     = UnitDec pos s ss (map (convertDec (snd (envStackLookupUnit rs [s]) : rs)) ds)
convertDec rs (ModDec pos s ds)         = ModDec pos s (map (convertDec (envStackLookupMod rs s : rs)) ds)
convertDec rs (NewDec pos s q tys)      = NewDec pos s q tys
convertDec rs (FunDec pos s ss ps ty t) = FunDec pos s ss ps ty (runM (convertTerm t) (\ x _ -> x) rs 0)
convertDec rs (SumDec pos s ss cs)      = SumDec pos s ss cs

data M a = M { runM :: forall b. (a -> Int -> b) -> [Env] -> Int -> b }

instance Monad M where
  return x = M (\ k rs -> k x)
  m >>= f = M (\ k rs -> runM m (\ x -> runM (f x) k rs) rs)

gen :: M Type.Type
gen = M (\ k rs i -> k (Type.Metavariable i) (i + 1))

gen1 :: a -> M Type.Type
gen1 _ = gen

lookupFunction :: [String] -> M ([String], Type.Type)
lookupFunction q = M (\ k r -> k (envStackLookupFunction r q))

envStackLookupFunction :: [Env] -> [String] -> ([String], Type.Type)
envStackLookupFunction [] q = error $ "envStackLookupFunction: " ++ show q
envStackLookupFunction (r:rs) q = maybe failure id (envLookupFunction r q)
  where failure = envStackLookupFunction rs q

envLookupFunction :: Env -> [String] -> Maybe ([String], Type.Type)
envLookupFunction r []    = error "envLookupFunction"
envLookupFunction r [s]   = lookup s (envFunctions r)
envLookupFunction r (s:q) = do r' <- lookup s (envModules r)
                               envLookupFunction r' q

lookupConstructor :: [String] -> M ([String], [Type.Type], Type.Type)
lookupConstructor q = M (\ k r -> k (envStackLookupConstructor r q))

envStackLookupConstructor :: [Env] -> [String] -> ([String], [Type.Type], Type.Type)
envStackLookupConstructor [] q = error $ "envStackLookupConstructor: " ++ show q
envStackLookupConstructor (r:rs) q = maybe failure id (envLookupConstructor r q)
  where failure = envStackLookupConstructor rs q

envLookupConstructor :: Env -> [String] -> Maybe ([String], [Type.Type], Type.Type)
envLookupConstructor r []    = error "envLookupConstructor"
envLookupConstructor r [s]   = lookup s (envConstructors r)
envLookupConstructor r (s:q) = do r' <- lookup s (envModules r)
                                  envLookupConstructor r' q

convertTerm :: Term -> M Term
convertTerm t =
  case t of
    ApplyTerm _ t1 t2 -> do
      m <- gen
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ ApplyTerm m t1' t2'
    BindTerm pos p t1 t2 -> do
      m <- gen
      p' <- convertPat p
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ BindTerm pos p' t1' t2'
    UnitTerm pos ->
      return $ UnitTerm pos
    UpperTerm pos _ _ s -> do
      (ss, ty) <- lookupFunction s
      ts' <- mapM gen1 ss
      ty' <- return $ Type.rename (zip ss ts') ty
      return $ UpperTerm pos ts' ty' s
    VariableTerm pos s ->
      return $ VariableTerm pos s
    t ->
      error $ "cote: " ++ show t

convertPat :: Pat -> M Pat
convertPat p =
  case p of
    AscribePat p ty -> do
      p' <- convertPat p
      return $ AscribePat p' ty
    LowerPat pos s -> do
      return $ LowerPat pos s
    TuplePat _ ps -> do
      m <- mapM gen1 ps
      ps' <- mapM convertPat ps
      return $ TuplePat m ps'
    UnderbarPat -> do
      return $ UnderbarPat
    UnitPat pos -> do
      return $ UnitPat pos
    -- This is wrong.
    UpperPat pos _ _ q ps -> do
      (ss, tys, ty) <- lookupConstructor q
      ms <- mapM gen1 ss
      tys' <- return $ map (Type.rename (zip ss ms)) tys
      ty' <- return $ Type.rename (zip ss ms) ty
      ps' <- mapM convertPat ps
      return $ UpperPat pos tys' ty' q ps'

convertType :: Typ -> Type.Type
convertType (ArrowTyp t1 t2)   = Type.Arrow (convertType t1) (convertType t2)
convertType (LowerTyp s)       = Type.Variable s
convertType (TupleTyp tys)     = Type.Tuple (map convertType tys)
convertType (UnitTyp _)        = Type.Unit
convertType (UpperTyp _ q tys) = Type.Variant q (map convertType tys)

{-

-- Add type metavariables to the syntax. This is done before type checking.
-- We also add the type to every upper-case variable so the type-checker does
-- not have to look it up.


data Result a where
  Return      :: a -> Result a
  Bind        :: Result b -> (b -> Result a) -> Result a
  Gen         :: Result Int
  Function    :: String -> Result ([String], Type.Type)
  Constructor :: String -> Result ([String], [Type.Type], Type.Type)

instance Monad Result where
  return = Return
  Return x >>= f = f x
  Bind m g >>= f = Bind m (\ x -> g x >>= f)
  m        >>= f = Bind m f

env :: [(String, ([String], Type.Type))]
env = [ ("Exit", ([], Type.Variant ["Output"] []))
      , ("Unreachable", (["a"], Type.Variable "a"))
      ]

constructorEnv :: [(String, ([String], [Type.Type], Type.Type))]
constructorEnv = [ ("Exit", ([], [], Type.Variant ["Output"] []))
                 ]

addMetavariables :: Program -> Program
addMetavariables (Program ds) = Program (reverse ds')
  where r = foldl arity env ds
        g = foldl constructors constructorEnv ds
        (ds', _) = foldl f ([], 0) ds
        f :: ([Dec], Int) -> Dec -> ([Dec], Int)
        f (ds', n) d = dec ds' g r n d

type Arity = [(String, ([String], Type.Type))]

arity :: [(String, ([String], Type.Type))] -> Dec -> [(String, ([String], Type.Type))]
arity r (FunDec _ s ss ps ty _) = (s, (ss, funType ps ty)) : r
arity r (SumDec _ s1 ss rs) = foldl f r rs
                              where f r (_, s2, tys) = (s2, (ss, constructorType tys [s1] ss)) : r
arity r (TagDec _ s ty) = (s, ([], typType ty)) : r
arity r (NewDec _ s1 "Escape" [ty1, ty2]) = (s1 ++ ".Catch", (["a"], Type.Arrow (Type.Arrow Type.Unit (Type.Variable "a"))
                                                                    (Type.Arrow (Type.Arrow ty1'
                                                                                (Type.Arrow (Type.Arrow ty2' (Type.Variable "a"))
                                                                                            (Type.Variable "a")))
                                                                                (Type.Variable "a"))))
                                          : (s1 ++ ".Throw", ([], Type.Arrow ty1' ty2'))
                                          : r
                                          where ty1' = typType ty1
                                                ty2' = typType ty2
arity r (NewDec _ s1 s2 tys) = lookupUnitArity s2 s1 tys ++ r
arity r (UnitDec _ _ _ _) = r

lookupUnitArity :: String -> String -> [Typ] -> Arity
lookupUnitArity name prefix tyArgs = undefined

type Constructors = [(String, ([String], [Type.Type], Type.Type))]

constructors :: [(String, ([String], [Type.Type], Type.Type))] -> Dec -> [(String, ([String], [Type.Type], Type.Type))]
constructors r (FunDec _ _ _ _ _ _) = r
constructors r (SumDec _ s1 ss rs) = foldl f r rs
                                     where f r (_, s2, tys) = (s2, (ss, map typType tys, Type.Variant s1 (map Type.Variable ss))) : r
constructors r (TagDec _ _ _) = r
constructors r (NewDec _ s1 s2 tys) = lookupUnitConstructors s2 s1 tys
constructors r (UnitDec _ _ _ _) = r

lookupUnitConstructors :: String -> String -> [Typ] -> Constructors
lookupUnitConstructors name prefix tyArgs = undefined

genMeta :: a -> Result Type.Type
genMeta _ = liftM Type.Metavariable Gen

-- data Dec = FunDec Pos String [String] [Pat] Typ Term
dec :: [Dec] -> [(String, ([String], [Type.Type], Type.Type))] -> [(String, ([String], Type.Type))] -> Int -> Dec -> ([Dec], Int)
dec ds g r n (FunDec pos s ss ps t e) = check n m
  where m = do ps' <- mapM pat ps
               t' <- term e
               return $ FunDec pos s ss ps' t t' : ds
        check n (Return e)               = (e, n)
        check n (Bind Gen k)             = check (n + 1) (k n)
        check n (Bind (Function s) k)    = check n (k (lookupJust s r))
        check n (Bind (Constructor s) k) = check n (k (lookupJust s g))
        check n (Bind (Return _) _)      = error "Compiler.Meta.dec: unreachable"
        check n (Bind (Bind _ _) _)      = error "Compiler.Meta.dec: unreachable"
dec ds g r n (SumDec pos s ss rs) = (SumDec pos s ss rs : ds, n)
dec ds g r n (TagDec pos s ty)    = (TagDec pos s ty : ds, n)
dec ds g r n (NewDec pos s1 s2 tys) = (NewDec pos s1 s2 tys : ds, n)
dec ds g r n (UnitDec pos s tys ds2) = withTypeVariables tys (f [] g r n ds2)
                                       where f ds2' g r n [] = (UnitDec pos s tys (reverse ds2') : ds, n)
                                             f ds2' g r n (d:ds) = undefined

withTypeVariables :: [String] -> ([Dec], Int) -> ([Dec], Int)
withTypeVariables = undefined

term :: Term -> Result Term
term (ApplyTerm _ t1 t2)  = do m <- genMeta ()
                               t1' <- term t1
                               t2' <- term t2
                               return $ ApplyTerm m t1' t2'
term (AscribeTerm p t ty) = do t' <- term t
                               return $ AscribeTerm p t' ty
term (BindTerm _ p t1 t2) = do m <- genMeta ()
                               p <- pat p
                               t1' <- term t1
                               t2' <- term t2
                               return $ BindTerm m p t1' t2'
term (CaseTerm _ t rs)    = do m <- genMeta ()
                               t' <- term t
                               rs' <- mapM rule rs
                               return $ CaseTerm m t' rs'
                            where rule (p, t) = do
                                    p' <- pat p
                                    t' <- term t
                                    return (p', t')
term (SeqTerm t1 t2)      = do t1' <- term t1
                               t2' <- term t2
                               return $ SeqTerm t1' t2'
term (TupleTerm p ts es)  = do ts' <-  mapM genMeta ts
                               es' <- mapM term es
                               return $ TupleTerm p ts' es'
term (UnitTerm p)         = return $ UnitTerm p
term (UpperTerm p _ _ s)  = do (ss, ty) <- Function s
                               ts' <- mapM genMeta ss
                               ty' <- return $ Type.rename (zip ss ts') ty
                               return $ UpperTerm p ts' ty' s
term (VariableTerm p s)   = return $ VariableTerm p s

pat :: Pat -> Result Pat
pat (AscribePat p ty) = do p' <- pat p
                           return $ AscribePat p' ty
pat (LowerPat pos x)  = return $ LowerPat pos x
pat (TuplePat ms ps)  = do ms' <- mapM genMeta ms
                           ps' <- mapM pat ps
                           return $ TuplePat ms' ps'
pat UnderbarPat       = return UnderbarPat
pat (UnitPat pos)     = return $ UnitPat pos
pat (UpperPat pos _ _ x ps)
                      = do (ss, tys, ty) <- Constructor x
                           ss' <- mapM genMeta ss
                           ty' <- return $ Type.rename (zip ss ss') ty
                           tys' <- return $ map (Type.rename (zip ss ss')) tys
                           ps' <- mapM pat ps
                           return $ UpperPat pos tys' ty' x ps'

-- Utility

lookupJust :: Eq a => a -> [(a, b)] -> b
lookupJust key = fromJust . lookup key

-}