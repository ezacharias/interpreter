module Compiler.Meta where

import           Data.Maybe      (fromMaybe)

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
envStackLookupUnit (r:rs) q = fromMaybe failure (envLookupUnit r q)
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
gatherDec l rs r (UnitDec _ s ss ds)     = envWithUnit r s (ss, foldl (gatherDec (s:l) (r:rs)) emptyEnv ds)

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
  where ps' = filter (\ (s2, _) -> notElem s2 ss) ps

funSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, ([String], Type.Type)) -> (String, ([String], Type.Type))
funSubstitute q1 q2 ps (s, (ss, ty)) = (s, (ss, typeSubstitute q1 q2 ps' ty))
  where ps' = filter (\ (s2, _) -> notElem s2 ss) ps

conSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, ([String], [Type.Type], Type.Type)) -> (String, ([String], [Type.Type], Type.Type))
conSubstitute = error "cs"

typeSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> Type.Type -> Type.Type
typeSubstitute q1 q2 ps (Type.Arrow ty1 ty2)  = Type.Arrow (typeSubstitute q1 q2 ps ty1) (typeSubstitute q1 q2 ps ty2)
typeSubstitute q1 q2 ps (Type.Metavariable i) = Type.Metavariable i
typeSubstitute q1 q2 ps (Type.Tuple tys)      = Type.Tuple (map (typeSubstitute q1 q2 ps) tys)
typeSubstitute q1 q2 ps Type.Unit             = Type.Unit
typeSubstitute q1 q2 ps (Type.Variable s)     = fromMaybe (Type.Variable s) (lookup s ps)
typeSubstitute q1 q2 ps (Type.Variant q tys)  = Type.Variant (fromMaybe q (f q1 q)) (map (typeSubstitute q1 q2 ps) tys)
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
convertDec rs (FunDec pos s ss ps ty t) = FunDec pos s ss ps ty (runM (convertTerm t) const rs 0)
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
envStackLookupFunction (r:rs) q = fromMaybe failure (envLookupFunction r q)
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
envStackLookupConstructor (r:rs) q = fromMaybe failure (envLookupConstructor r q)
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
    AscribeTerm pos t ty -> do
      t' <- convertTerm t
      return $ AscribeTerm pos t' ty
    BindTerm pos p t1 t2 -> do
      m <- gen
      p' <- convertPat p
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ BindTerm pos p' t1' t2'
    CaseTerm _ t rs -> do
      m <- gen
      t' <- convertTerm t
      rs' <- mapM convertRule rs
      return $ CaseTerm m t' rs'
    SeqTerm t1 t2 -> do
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ SeqTerm t1' t2'
    TupleTerm pos _ ts -> do
      ms <- mapM gen1 ts
      ts' <- mapM convertTerm ts
      return $ TupleTerm pos ms ts'
    UnitTerm pos ->
      return $ UnitTerm pos
    UpperTerm pos _ _ s -> do
      (ss, ty) <- lookupFunction s
      ts' <- mapM gen1 ss
      let ty' = Type.rename (zip ss ts') ty
      return $ UpperTerm pos ts' ty' s
    VariableTerm pos s ->
      return $ VariableTerm pos s

convertRule :: (Pat, Term) -> M (Pat, Term)
convertRule (p, t) = do
  p' <- convertPat p
  t' <- convertTerm t
  return (p', t')

convertPat :: Pat -> M Pat
convertPat p =
  case p of
    AscribePat p ty -> do
      p' <- convertPat p
      return $ AscribePat p' ty
    LowerPat pos s ->
      return $ LowerPat pos s
    TuplePat _ ps -> do
      m <- mapM gen1 ps
      ps' <- mapM convertPat ps
      return $ TuplePat m ps'
    UnderbarPat ->
      return UnderbarPat
    UnitPat pos ->
      return $ UnitPat pos
    -- This is wrong.
    UpperPat pos _ _ q ps -> do
      (ss, tys, ty) <- lookupConstructor q
      ms <- mapM gen1 ss
      let tys' = map (Type.rename (zip ss ms)) tys
      let ty' = Type.rename (zip ss ms) ty
      ps' <- mapM convertPat ps
      return $ UpperPat pos tys' ty' q ps'

convertType :: Typ -> Type.Type
convertType (ArrowTyp t1 t2)   = Type.Arrow (convertType t1) (convertType t2)
convertType (LowerTyp s)       = Type.Variable s
convertType (TupleTyp tys)     = Type.Tuple (map convertType tys)
convertType (UnitTyp _)        = Type.Unit
convertType (UpperTyp _ q tys) = Type.Variant q (map convertType tys)
