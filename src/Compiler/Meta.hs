module Compiler.Meta where

import Control.Applicative (Alternative, empty, (<|>))
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

tr :: Show a => a -> a
tr x = trace (show x) x

addMetavariables :: Syntax.Program -> Syntax.Program
addMetavariables p = convertProgram (programEnv p) p

-- An environment is a possible old path, the full path, the local type bindings, and the declarations.
-- The old path is the name of the environment without accounting for new, so it is only different for
-- units. We use the old path to identify units which are primitives.
data Env = Env [Frame]
           deriving (Show)
type Frame = (Maybe Type.Path, Type.Path, [(String, Type.Type)], [Syntax.Dec])
--- Actualyl, I think the old path is only used by primitives.

programEnv :: Syntax.Program -> Env
programEnv (Syntax.Program ds) = Env [(Nothing, Type.Path [], [], ds)]

envPath :: Env -> Type.Path
envPath (Env []) = unreachable "envPath"
envPath (Env ((_, q, _, _) : _)) = q

envPush :: Env -> Frame -> Env
envPush (Env r) x = Env (x:r)

envAddTypeVariables :: Env -> [String] -> Env
envAddTypeVariables r vs = envPush r (Nothing, Type.Path [], typeVariables vs, [])

typeVariables :: [String] -> [(String, Type.Type)]
typeVariables vs = map (\ v -> (v, Type.Variable v)) vs

convertProgram ::  Env -> Syntax.Program -> Syntax.Program
convertProgram r (Syntax.Program ds) = Syntax.Program (map (convertDec r) ds)

convertDec :: Env -> Syntax.Dec -> Syntax.Dec
convertDec r t =
  case t of
    Syntax.FunDec pos _ _ s vs ps ty t -> run (envAddTypeVariables r vs) $ do
      tys' <- mapM getPatType ps
      ty' <- convertType ty
      t' <- convertTerm t
      return $ Syntax.FunDec pos tys' ty' s vs ps ty t'
    Syntax.ModDec pos s vs ds ->
      let q' = Type.pathAddName (envPath r) (Type.Name s (map Type.Variable vs))
          r' = (envPush r (Nothing, q', typeVariables vs, ds))
       in Syntax.ModDec pos s vs (map (convertDec r') ds)
    Syntax.NewDec pos _ s vs q ->
      let r' = envAddTypeVariables r vs
          q' = Type.pathAddName (envPath r) (Type.Name s (map Type.Variable vs))
          q'' = envPath (envGetUnit r' (envConvertPath r' q) q')
       in Syntax.NewDec pos q'' s vs q
    Syntax.SubDec pos _ s vs q ->
      let r' = envAddTypeVariables r vs
          q' = envPath (envGetMod r' (envConvertPath r' q))
       in Syntax.SubDec pos q' s vs q
    -- Do we want to add some information here?
    Syntax.SumDec pos s ss cs ->
      Syntax.SumDec pos s ss cs
    Syntax.UnitDec pos s vs ds ->
      let q' = Type.pathAddName (envPath r) (Type.Name s (map Type.Variable vs))
          r' = envPush r (Nothing, q', typeVariables vs, ds)
       in Syntax.UnitDec pos s vs (map (convertDec r') ds)

convertTerm :: Syntax.Term -> M Syntax.Term
convertTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      ty <- gen
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Syntax.ApplyTerm ty t1 t2
    Syntax.BindTerm _ p t1 t2 -> do
      ty <- gen
      p <- convertPat p
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Syntax.BindTerm ty p t1 t2
    Syntax.CaseTerm _ t rs -> do
      ty <- gen
      t <- convertTerm t
      rs <- mapM convertRule rs
      return $ Syntax.CaseTerm ty t rs
    Syntax.ForTerm _ _ ps t1 t2 -> do
      tys <- case ps of
        [] -> return [Type.Unit]
        (_:_) -> mapM (const gen) ps
      ty <- gen
      ps <- mapM convertPat ps
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Syntax.ForTerm tys ty ps t1 t2
    Syntax.SeqTerm t1 t2 -> do
      t1 <- convertTerm t1
      t2 <- convertTerm t2
      return $ Syntax.SeqTerm t1 t2
    Syntax.StringTerm pos x ->
      return $ Syntax.StringTerm pos x
    Syntax.TupleTerm pos _ ts -> do
      tys <- mapM (const gen) ts
      ts <- mapM convertTerm ts
      return $ Syntax.TupleTerm pos tys ts
    Syntax.UnitTerm pos ->
      return $ Syntax.UnitTerm pos
    Syntax.UpperTerm pos _ _ q -> do
      q' <- convertPath q
      (q', ty) <- getFun q'
      return $ Syntax.UpperTerm pos q' ty q
    Syntax.VariableTerm pos s ->
      return $ Syntax.VariableTerm pos s
    t ->
      todo $ "convertTerm: " ++ show t

-- Converts to a local Type.Path.
convertPath :: Syntax.Path -> M Type.Path
convertPath q = do
  r <- getEnv
  envConvertPath r q

envConvertPath :: Env -> Syntax.Path -> Type.Path
envConvertPath r q = Type.Path $ map (envConvertName r) q

envConvertName :: Env -> Syntax.Name -> Type.Name
envConvertName r (s, tys) = Type.Name s (map (envConvertType r) tys)

convertRule :: Syntax.Rule -> M Syntax.Rule
convertRule (pat, t) = do
  pat <- convertPat pat
  t <- convertTerm t
  return (pat, t)

convertPat :: Syntax.Pat -> M Syntax.Pat
convertPat p =
  case p of
    Syntax.AscribePat pos p ty -> do
      p <- convertPat p
      return $ Syntax.AscribePat pos p ty
    Syntax.LowerPat pos s ->
      return $ Syntax.LowerPat pos s
    Syntax.TuplePat pos _ ps -> do
      ps <- mapM convertPat ps
      tys <- mapM (const gen) ps
      return $ Syntax.TuplePat pos tys ps
    Syntax.UnderbarPat ->
      return $ Syntax.UnderbarPat
    Syntax.UnitPat pos ->
      return $ Syntax.UnitPat pos
    Syntax.UpperPat pos _ _ q ps -> do
      (ss, ty, tys) <- getConstructor (createPath q [])
      ds <- mapM (const gen) ss
      ty <- return $ Type.substitute (zip ss ds) ty
      tys <- return $ map (Type.substitute (zip ss ds)) tys
      ps <- mapM convertPat ps
      return $ Syntax.UpperPat pos tys ty q ps

getConstructor :: Type.Path -> M ([String], Type.Type, [Type.Type])
getConstructor q = do
  r <- getEnv
  return $ envGetConstructor r q

envGetConstructor :: Env -> Type.Path -> ([String], Type.Type, [Type.Type])
envGetConstructor r (Type.Path [n])    = envGetConstructorWithName r n
envGetConstructor r (Type.Path (n:ns)) = envGetConstructorWithFields (envGetModWithName r n) (Type.Path ns)
envGetConstructor r (Type.Path [])     = unreachable "envGetConstructor"

envGetConstructorWithName :: Env -> Type.Name -> ([String], Type.Type, [Type.Type])
envGetConstructorWithName (Env []) q = unreachable $ "envGetConstructorWithName: " ++ show q
envGetConstructorWithName (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetConstructorWithName: " ++ show q1
envGetConstructorWithName (Env r@((Nothing, q, _, ds) : r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetConstructorWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.SumDec _ s2 ss cs ->
              let hasConstructor (_, s3, tys) | s1 == s3 =
                    let tys' = map (envConvertType (envAddTypeVariables (Env r) ss)) tys
                        ty' = Type.Variant (Type.pathAddName q (Type.Name s2 (map Type.Variable ss)))
                     in Just (ss, ty', tys')
                  hasConstructor _ =
                    Nothing
               in search hasConstructor cs
            _ ->
              Nothing

envGetConstructorWithFields :: Env -> Type.Path -> ([String], Type.Type, [Type.Type])
envGetConstructorWithFields r q = todo "envGetConstructorWithFields"

-- Returns returns the full path of the function as well as the type.
getFun :: Type.Path -> M ([String], Type.Type)
getFun q = do
  r <- getEnv
  return $ envGetFun r q

envGetFun :: Env -> Type.Path -> ([String], Type.Type)
envGetFun r (Type.Path [n])    = envGetFunWithName r n
envGetFun r (Type.Path (n:ns)) = envGetFunWithFields (envGetModWithName r n) (Type.Path ns)
envGetFun r (Type.Path [])     = unreachable "envGetFun"

-- Should this check the static path?
envGetFunWithName :: Env -> Type.Name -> ([String], Type.Type)
envGetFunWithName (Env []) (Type.Name "Continue" _) = continuePrimitive
envGetFunWithName (Env []) (Type.Name "Exit" _) = exitPrimitive
envGetFunWithName (Env []) (Type.Name "Write" _) = writePrimitive
envGetFunWithName (Env []) (Type.Name "Unreachable" _) = (["a"], Type.Variable "a")
envGetFunWithName (Env []) q = unreachable $ "envGetFunWithName: " ++ show q
envGetFunWithName (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetFunWithName: " ++ show q1
envGetFunWithName (Env r@((Nothing, q, _, ds) : r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetFunWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps ty t | s1 == s2 ->
              let r'' = Env ((Nothing, Type.Path [], map (\ s -> (s, Type.Variable s)) ss, []) : r)
               in Just $ (ss, envSigType r'' ps ty)
            Syntax.SumDec _ s2 ss cs ->
              let hasConstructor (_, s3, tys) | s1 == s3 =
                    let tys' = map (envConvertType (envAddTypeVariables (Env r) ss)) tys
                        ty' = Type.Variant (Type.pathAddName q (Type.Name s2 (map Type.Variable ss)))
                     in Just (ss, foldr Type.Arrow ty' tys')
                  hasConstructor _ =
                    Nothing
               in search hasConstructor cs
            _ ->
              Nothing

envGetFunWithFields :: Env -> Type.Path -> ([String], Type.Type)
envGetFunWithFields (Env []) (Type.Path [Type.Name "Continue" _]) = continuePrimitive
envGetFunWithFields (Env []) (Type.Path [Type.Name "Exit" _]) = exitPrimitive
envGetFunWithFields (Env []) (Type.Path [Type.Name "Write" _]) = writePrimitive
envGetFunWithFields (Env []) n = unreachable $ "envGetFunWithFields1: " ++ show n
envGetFunWithFields _ (Type.Path []) = unreachable "envGetFunWithFields 2"
envGetFunWithFields (Env r@((Just (Type.Path [Type.Name "Escape" [ty1, ty2]]), _, _, _):r')) (Type.Path [Type.Name "Catch" []]) = catchPrimitive ty1 ty2
envGetFunWithFields (Env r@((Just (Type.Path [Type.Name "Escape" [ty1, ty2]]), _, _, _):r')) (Type.Path [Type.Name "Throw" []]) = throwPrimitive ty1 ty2
envGetFunWithFields (Env r@((_, q, _, ds):r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields 6"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps ty t | s1 == s2 ->
              let r'' = Env ((Nothing, Type.Path [], map (\ s -> (s, Type.Variable s)) ss, []) : r)
               in Just $ (ss, envSigType r'' ps ty)
            _ ->
              Nothing
envGetFunWithFields (Env r@((_, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields 7"
        check (Just r'') = envGetFunWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just $ Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r)
            Syntax.NewDec _ _ s2 q' tys' | s1 == s2 ->
               let q'' = createPath q' (map (envConvertType (Env r)) tys')
                in Just $ envGetUnit (Env r) q'' (Type.pathAddName q (Type.Name s1 tys))
            _ ->
              Nothing

exitPrimitive :: ([String], Type.Type)
exitPrimitive = ([], Type.Variant (Type.Path [Type.Name "Output" []]))

writePrimitive :: ([String], Type.Type)
writePrimitive = ([], Type.Arrow Type.String
                                 (Type.Arrow (Type.Variant (Type.Path [Type.Name "Output" []]))
                                             (Type.Variant (Type.Path [Type.Name "Output" []]))))

continuePrimitive :: ([String], Type.Type)
continuePrimitive = ([], Type.Arrow (Type.Arrow Type.Unit
                                                (Type.Variant (Type.Path [Type.Name "Output" []])))
                                    (Type.Variant (Type.Path [Type.Name "Output" []])))

catchPrimitive :: Type.Type -> Type.Type -> ([String], Type.Type)
catchPrimitive ty1 ty2 =
  ( ["c"]
  , Type.Arrow (Type.Arrow Type.Unit
                           (Type.Variable "c"))
               (Type.Arrow (Type.Arrow ty1
                                       (Type.Arrow (Type.Arrow ty2
                                                               (Type.Variable "c"))
                                                   (Type.Variable "c")))
                           (Type.Variable "c"))
  )

throwPrimitive :: Type.Type -> Type.Type -> ([String], Type.Type)
throwPrimitive ty1 ty2 =
  ( []
  , Type.Arrow ty1 ty2
  )

envSigType :: Env -> [Syntax.Pat] -> Syntax.Type -> Type.Type
envSigType r [] ty = envConvertType r ty
envSigType r (p:ps) ty = Type.Arrow (envPatType r p) (envSigType r ps ty)

convertType :: Syntax.Typ -> M Type.Type
convertType ty = do
  r <- getEnv
  return $ envConvertType r ty

envConvertType :: Env -> Syntax.Type -> Type.Type
envConvertType r ty =
  case ty of
    Syntax.ArrowType ty1 ty2 -> Type.Arrow (envConvertType r ty1) (envConvertType r ty2)
    Syntax.LowerType x -> envGetTypeVariable r x
    Syntax.TupleType tys -> Type.Tuple (map (envConvertType r) tys)
    Syntax.UnitType _ -> Type.Unit
    Syntax.UpperType _ [("Result", [])] -> envGetType r (createPath ["Result"] (map (envConvertType r) tys))
    Syntax.UpperType _ q -> envGetType r (createPath q (map (envConvertType r) tys))

envGetTypeVariable :: Env -> String -> Type.Type
envGetTypeVariable (Env []) s = unreachable $ "envGetTypeVariable: " ++ s
envGetTypeVariable (Env ((_, _, xs, _) : r)) s = fromMaybe (envGetTypeVariable (Env r) s) (lookup s xs)

getPatType :: Syntax.Pat -> M Type.Type
getPatType p = do
  r <- getEnv
  return $ envPatType r p

-- For now constructor patterns in function declarations must have ascriptions.
envPatType :: Env -> Syntax.Pat -> Type.Type
envPatType r p =
  case p of
    Syntax.AscribePat _ p ty -> envConvertType r ty
    Syntax.LowerPat _ x -> unreachable "envPatType"
    Syntax.TuplePat _ _ ps -> Type.Tuple (map (envPatType r) ps)
    Syntax.UnderbarPat -> unreachable "envPatType"
    Syntax.UnitPat _ -> Type.Unit
    Syntax.UpperPat _ _ _ q ps -> unreachable "envPatType"

createPath :: [String] -> [Type.Type] -> Type.Path
createPath [s] tys = Type.Path [Type.Name s tys]
createPath (s:ss) tys = Type.nameAddPath (Type.Name s []) (createPath ss tys)
createPath _ _ = unreachable "createPath"

-- Lookup a variant type with the path in the environment.
envGetType :: Env -> Type.Path -> Type.Type
envGetType r (Type.Path []) = unreachable "envGetType"
envGetType r (Type.Path [n]) = envGetTypeWithName r n
envGetType r (Type.Path (n:ns)) = envGetTypeWithFields (envGetModWithName r n) (Type.Path ns)

envGetTypeWithName :: Env -> Type.Name -> Type.Type
envGetTypeWithName (Env []) (Type.Name "Output" []) = Type.Variant (Type.Path [Type.Name "Output" []])
envGetTypeWithName (Env []) (Type.Name "String" []) = Type.String
envGetTypeWithName (Env []) x = unreachable $ "envGetTypeWithName 1: " ++ show x
-- envGetTypeWithName (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetTypeWithName 2: " ++ show q2
envGetTypeWithName (Env r@((_, q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetTypeWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.SumDec _ s2 ss _ | s1 == s2 ->
              Just (Type.Variant (Type.pathAddName q (Type.Name s1 tys)))
            _ ->
              Nothing

envGetTypeWithFields :: Env -> Type.Path -> Type.Type
envGetTypeWithFields (Env []) _ = unreachable "envGetTypeWithFields"
envGetTypeWithFields _ (Type.Path []) = unreachable "envGetTypeWithFields"
envGetTypeWithFields (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetTypeWithFields: " ++ show q1
envGetTypeWithFields (Env r@((Nothing, q, _, ds):r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetTypeWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.SumDec _ s2 ss _ | s1 == s2 ->
              Just (Type.Variant (Type.pathAddName q (Type.Name s1 tys)))
            _ ->
              Nothing
envGetTypeWithFields (Env r@((Nothing, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetTypeWithFields"
        check (Just r'') = envGetTypeWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just $ Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r)
            Syntax.NewDec _ _ s2 q' tys' | s1 == s2 ->
               let q'' = createPath q' (map (envConvertType (Env r)) tys')
                in Just $ envGetUnit (Env r) q'' (Type.pathAddName q (Type.Name s1 tys))
            _ ->
              Nothing

primitiveEscape :: Type.Type -> Type.Type -> Type.Path -> Env
primitiveEscape ty1 ty2 q = Env [(Just (Type.Path [Type.Name "Escape" [ty1, ty2]]), q, [], [])]

-- The second path is the new name.
envGetUnit :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnit r (Type.Path []) = unreachable "envUnit"
envGetUnit r (Type.Path [n]) = envGetUnitWithName r n
envGetUnit r (Type.Path (n:ns)) = envGetUnitWithFields (envGetModWithName r n) (Type.Path ns)

envGetUnitWithName :: Env -> Type.Name -> (Type.Path -> Env)
envGetUnitWithName (Env []) (Type.Name "Escape" [ty1, ty2]) = primitiveEscape ty1 ty2
envGetUnitWithName (Env []) n = unreachable $ "envGetUnitWithName: " ++ show n
envGetUnitWithName (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetUnitWithName: " ++ show q1
envGetUnitWithName (Env r@((Nothing, q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetUnitWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              -- I think we need to change this for applicative.
              Just $ \ q' -> Env ((Just (Type.pathAddName q (Type.Name s1 tys)), q', zip s3s tys, ds) : r)
            _ ->
              Nothing

envGetUnitWithFields :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnitWithFields (Env []) _ = unreachable "envGetUnitWithFields"
envGetUnitWithFields _ (Type.Path []) = unreachable "envGetUnitWithFields"
envGetUnitWithFields (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetUnitWithFields: " ++ show q1
envGetUnitWithFields (Env r@((Nothing, q, _, ds):r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              Just $ \ q' -> Env ((Just (todo "envGetUnitWithFields"), q', zip s3s tys, ds) : r)
            _ ->
              Nothing
envGetUnitWithFields (Env r@((Nothing, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just r'') = envGetUnitWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just $ Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r)
            Syntax.NewDec _ _ s2 q' tys' | s1 == s2 ->
               let q'' = createPath q' (map (envConvertType (Env r)) tys')
                in Just $ envGetUnit (Env r) q'' (Type.pathAddName q (Type.Name s1 tys))
            _ ->
              Nothing

envGetMod :: Env -> Type.Path -> Env
envGetMod r (Type.Path []) = unreachable "envGetMod"
envGetMod r (Type.Path (n:ns)) = envGetModWithFields (envGetModWithName r n) (Type.Path ns)

envGetModWithName :: Env -> Type.Name -> Env
envGetModWithName (Env []) (Type.Name "Root" []) = Env []
envGetModWithName (Env []) n = unreachable $ "envGetModWithName: " ++ show n
envGetModWithName (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetModWithName: " ++ show q1
envGetModWithName (Env r@((Nothing, q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetModWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.NewDec _ ty2s s2 q' tys' | s1 == s2 ->
              let q'' = createPath q' (map (envConvertType (Env r)) tys')
               in Just $ (envGetUnit (Env r)) q'' (Type.pathAddName q (Type.Name s1 tys))
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just $ Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r)
            Syntax.SubDec _ s2 q2 | s1 == s2 ->
              -- Substitutions start searching the environment above the declaration, hence r'.
              Just $ envGetMod (Env r') (createPath q2 [])
            _ ->
              Nothing

envGetModWithFields :: Env -> Type.Path -> Env
envGetModWithFields r (Type.Path []) = r
envGetModWithFields (Env []) n = unreachable $ "envGetModWithFields: " ++ show n
envGetModWithFields (Env r@((Just q1, _, _, _):r')) q2 = unreachable $ "envGetModWithFields: " ++ show q1
envGetModWithFields (Env r@((Nothing, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetModWithFields"
        check (Just r'') = envGetModWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just $ Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r)
            Syntax.NewDec _ _ s2 q' tys' | s1 == s2 ->
               let q'' = createPath q' (map (envConvertType (Env r)) tys')
                in Just $ envGetUnit (Env r) q'' (Type.pathAddName q (Type.Name s1 tys))
            _ ->
              Nothing

convertQual :: [String] -> [Type.Type] -> Type.Path
convertQual ss tys = Type.Path (f ss)
  where f [] = unreachable "convertQual"
        f [s] = [Type.Name s tys]
        f (s:ss) = Type.Name s [] : f ss

run :: Env -> M Syntax.Dec -> Syntax.Dec
run r m =  runM m r k 0
  where k x _ = x

newtype M a = M { runM :: Env -> (a -> Int -> Syntax.Dec) -> Int -> Syntax.Dec }

instance Monad M where
  return x = M (\ r k -> k x)
  m >>= f = M (\ r k -> runM m r (\ x -> runM (f x) r k))

getEnv :: M Env
getEnv = M f
  where f r k = k r

withEnv :: Env -> M a -> M a
withEnv r' m = M f
  where f r k = runM m r' k

gen :: M Type.Type
gen = M f
  where f r k i = k (Type.Metavariable i) (i + 1)

search :: Alternative m => (a -> m b) -> [a] -> m b
search f = choice . map f
-- search f [] = empty
-- search f (x:xs) = search f xs <|> f x -- maybe (search f xs) Just (f x)

choice :: Alternative m => [m a] -> m a
choice []     = empty
choice (x:xs) = x <|> choice xs







funType :: [Syntax.Pat] -> Syntax.Type -> Type.Type
funType []     t = typeType t
funType (p:ps) t = Type.Arrow (patType p) (funType ps t)

-- | This can only be used for patterns required to be fully typed.
patType :: Syntax.Pat -> Type.Type
patType (Syntax.AscribePat _ _ p ty) = typeType ty -- not sure about this
patType (Syntax.LowerPat _ s)    = error "Compiler.Syntax.patType"
patType (Syntax.TuplePat _ _ ps) = Type.Tuple (map patType ps)
patType Syntax.UnderbarPat       = error "Compiler.Syntax.patType"
patType (Syntax.UnitPat _)       = Type.Unit
patType (Syntax.UpperPat _ _ _ _ _ _) = error "Syntax.patType: not yet supported"

typeType :: Syntax.Type -> Type.Type
typeType (Syntax.ArrowType ty1 ty2)  = Type.Arrow (typeType ty1) (typeType ty2)
typeType (Syntax.LowerType s)        = Type.Variable s
typeType (Syntax.TupleType tys)      = Type.Tuple (map typeType tys)
typeType (Syntax.UnitType _)         = Type.Unit
typeType (Syntax.UpperType _ [("String", [])]) = Type.String -- fix this
typeType (Syntax.UpperType _ q) = Type.Variant (createPath q)

createPath :: Syntax.Path -> Type.Path
createPath q = Type.Path (map f q)
  where f (s, tys) = Type.Name s (map typeType tys)







todo :: String -> a
todo s = error $ "todo: Meta." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Meta." ++ s

{-
addMetavariables :: Program -> Program
addMetavariables p = convertProgram (gatherProgram p) p


--------------------------------------------------------------------------------
-- Gather the top-level types.
--------------------------------------------------------------------------------

data Env = Env
             { envUnits        :: [(String, ([String], Env))]
             , envModules      :: [(String, Either [String] Env)]
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
                 [ ( "Root"
                   , Left []
                   )
                 ]
                 [ ( "Concatenate"
                   , ([], Type.Arrow (Type.Tuple [Type.String, Type.String]) Type.String)
                   )
                 , ( "Continue"
                   , ([], Type.Arrow (Type.Arrow Type.Unit (Type.Variant ["Output"] [])) (Type.Variant ["Output"] []))
                   )
                 , ( "Exit"
                   , ([], Type.Variant ["Output"] [])
                   )
                 , ( "Show"
                   , (["a"], Type.Arrow (Type.Variable "a") Type.String)
                   )
                 , ( "Write"
                   , ([], Type.Arrow Type.String (Type.Arrow (Type.Variant ["Output"] []) (Type.Variant ["Output"] [])))
                   )
                 , ( "Unreachable"
                   , (["a"], Type.Variable "a")
                   )
                 ]
                 [ ( "Continue"
                   , ([], [Type.Arrow Type.Unit (Type.Variant ["Output"] [])], Type.Variant ["Output"] [])
                   )
                 , ( "Exit"
                   , ([], [], Type.Variant ["Output"] [])
                   )
                 , ( "Write"
                   , ([], [Type.String, Type.Variant ["Output"] []], Type.Variant ["Output"] [])
                   )
                 ]

envWithUnit :: Env -> String -> ([String], Env) -> Env
envWithUnit (Env x1s x2s x3s x4s) s x = Env ((s,x):x1s) x2s x3s x4s

envWithModule :: Env -> String -> Env -> Env
envWithModule (Env x1s x2s x3s x4s) s x = Env x1s ((s, Right x):x2s) x3s x4s

envWithSubstitution :: Env -> String -> [String] -> Env
envWithSubstitution (Env x1s x2s x3s x4s) s x = Env x1s ((s, Left x):x2s) x3s x4s

envWithFunction :: Env -> String -> ([String], Type.Type) -> Env
envWithFunction (Env x1s x2s x3s x4s) s x = Env x1s x2s ((s,x):x3s) x4s

envWithConstructor :: Env -> String -> ([String], [Type.Type], Type.Type) -> Env
envWithConstructor (Env x1s x2s x3s x4s) s x = Env x1s x2s x3s ((s,x):x4s)

envStackLookupUnit :: [Env] -> [String] -> ([String], Env)
envStackLookupUnit rs []    = error "envStackLookupUnit"
envStackLookupUnit rs [s]   = envStackLookupUnit1 rs s
envStackLookupUnit rs (s:q) = envLookupUnit1 (envResolve (envStackLookupMod1 rs s) q)

{-
envStackLookupUnit :: [Env] -> [String] -> ([String], Env)
envStackLookupUnit [] q = error $ "envStackLookupUnit: " ++ show q
envStackLookupUnit (r:rs) q = fromMaybe failure (envLookupUnit r q)
  where failure = envStackLookupUnit rs q

envLookupUnit :: Env -> [String] -> Maybe ([String], Env)
envLookupUnit r []    = error "envLookupUnit"
envLookupUnit r [s]   = lookup s (envUnits r)
envLookupUnit r (s:q) = do r <- lookup s (envModules r)
                           envLookupUnit r q
-}

envStackLookupMod :: [Env] -> [String] -> Env
envStackLookupMod rs []    = last rs
envStackLookupMod rs [s]   = envStackLookupMod1 rs s
envStackLookupMod rs (s:q) = envLookupMod1 (envResolve (envStackLookupMod1 rs s) q)

{-
envStackLookupMod :: [Env] -> [String] -> Env
envStackLookupMod [] q = error $ "envStackLookupMod: " ++ show q
envStackLookupMod (r:rs) q = fromMaybe failure (envLookupMod r q)
  where failure = envStackLookupMod rs q

envLookupMod :: Env -> [String] -> Maybe Env
envLookupMod r []    = error "envLookupMod"
envLookupMod r [s]   = lookup s (envModules r)
envLookupMod r (s:q) = do r <- lookup s (envModules r)
                          envLookupMod r q
-}

envStackLookupFunction :: [Env] -> [String] -> ([String], Type.Type)
envStackLookupFunction r []    = error "envStackLookupFunction"
envStackLookupFunction r [s]   = envStackLookupFunction1 r s
envStackLookupFunction r (s:q) = envLookupFunction1 (envResolve (envStackLookupMod1 r s) q)

envStackLookupConstructor :: [Env] -> [String] -> ([String], [Type.Type], Type.Type)
envStackLookupConstructor r []    = error "envStackLookupConstructor"
envStackLookupConstructor r [s]   = envStackLookupConstructor1 r s
envStackLookupConstructor r (s:q) = envLookupConstructor1 (envResolve (envStackLookupMod1 r s) q)

{-
envStackLookupConstructor :: [Env] -> [String] -> ([String], [Type.Type], Type.Type)
envStackLookupConstructor [] q = error $ "envStackLookupConstructor: " ++ show q
envStackLookupConstructor (r:rs) q = fromMaybe failure (envLookupConstructor r q)
  where failure = envStackLookupConstructor rs q
-}

envStackLookupUnit1 :: [Env] -> String -> ([String], Env)
envStackLookupUnit1 []     s = error $ "envStackLookupUnit1: " ++ s
envStackLookupUnit1 (r:rs) s = fromMaybe (envStackLookupUnit1 rs s) (lookup s (envUnits r))

envStackLookupMod1 :: [Env] -> String -> Env
envStackLookupMod1 []     s = error $ "envStackLookupMod1: " ++ s
envStackLookupMod1 (r:rs) s = case lookup s (envModules r) of
                                Nothing -> envStackLookupMod1 rs s
                                Just (Left []) -> r
                                Just (Left q)  -> envStackLookupMod rs q
                                Just (Right r) -> r

envStackLookupFunction1 :: [Env] -> String -> ([String], Type.Type)
envStackLookupFunction1 []     s = error $ "envStackLookupFunction1: " ++ s
envStackLookupFunction1 (r:rs) s = fromMaybe (envStackLookupFunction1 rs s) (lookup s (envFunctions r))

envStackLookupConstructor1 :: [Env] -> String -> ([String], [Type.Type], Type.Type)
envStackLookupConstructor1 []     s = error $ "envStackLookupConstructor1: " ++ s
envStackLookupConstructor1 (r:rs) s = fromMaybe (envStackLookupConstructor1 rs s) (lookup s (envConstructors r))

envResolve :: Env -> [String] -> (Env, String)
envResolve r []    = error "envLookupQualifier"
envResolve r [s]   = (r, s)
envResolve r (s:q) = envResolve (envLookupMod1 (r, s)) q

envLookupUnit1 :: (Env, String) -> ([String], Env)
envLookupUnit1 (r, s) = fromMaybe (error "envLookupUnit1") (lookup s (envUnits r))

envLookupMod1 :: (Env, String) -> Env
envLookupMod1 (r, s) = case lookup s (envModules r) of
                         Nothing -> error "envLookupMod1"
                         Just (Left _) -> error "envLookupMod1"
                         Just (Right r) -> r

envLookupFunction1 :: (Env, String) -> ([String], Type.Type)
envLookupFunction1 (r, s) = fromMaybe (error "envLookupFunction1") (lookup s (envFunctions r))

{-
envLookupFunction :: Env -> [String] -> Maybe ([String], Type.Type)
envLookupFunction r []    = error "envLookupFunction"
envLookupFunction r [s]   = lookup s (envFunctions r)
envLookupFunction r (s:q) = do r' <- lookup s (envModules r)
                               envLookupFunction r' q
-}

envLookupConstructor1 :: (Env, String) -> ([String], [Type.Type], Type.Type)
envLookupConstructor1 (r, s) = fromMaybe (error "envLookupConstructor1") (lookup s (envConstructors r))

{-
envLookupConstructor :: Env -> [String] -> Maybe ([String], [Type.Type], Type.Type)
envLookupConstructor r []    = error "envLookupConstructor"
envLookupConstructor r [s]   = lookup s (envConstructors r)
envLookupConstructor r (s:q) = do r' <- lookup s (envModules r)
                                  envLookupConstructor r' q
-}



gatherProgram :: Program -> Env
gatherProgram (Program ds) = foldl (gatherDec [] []) builtinEnv ds

gatherDec :: [String] -> [Env] -> Env -> Dec -> Env
gatherDec l rs r (FunDec _ _ _ s ss ps ty _) = envWithFunction r s (ss, funType ps ty)
gatherDec l rs r (ModDec _ s ds)             = envWithModule r s $ foldl (gatherDec (s:l) (r:rs)) emptyEnv ds
gatherDec l rs r (NewDec _ _ s q tys)        = envWithModule r s $ unitApply q (s:l) (envStackLookupUnit (r:rs) q) (map convertType tys)
gatherDec l rs r (SumDec _ s ss cs)          = foldl (gatherConstructor (reverse (s:l)) ss) r cs
gatherDec l rs r (UnitDec _ s ss ds)         = envWithUnit r s (ss, foldl (gatherDec (s:l) (r:rs)) emptyEnv ds)
gatherDec l rs r (SubDec _ s q)              = envWithSubstitution r s q

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

modSubstitute :: [String] -> [String] -> [(String, Type.Type)] -> (String, Either [String] Env) -> (String, Either [String] Env)
modSubstitute q1 q2 ps (s, Left x)  = (s, Left x)
modSubstitute q1 q2 ps (s, Right r) = (s, Right (envSubstitute q1 q2 ps r))

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
typeSubstitute q1 q2 ps Type.String           = Type.String
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

convertProgram :: Env -> Program -> Program
convertProgram r (Program ds) = Program (map (convertDec [r]) ds)

convertDec :: [Env] -> Dec -> Dec
convertDec rs (UnitDec pos s ss ds)         = UnitDec pos s ss (map (convertDec (snd (envStackLookupUnit rs [s]) : rs)) ds)
convertDec rs (ModDec pos s ds)             = ModDec pos s (map (convertDec (envStackLookupMod rs [s] : rs)) ds)
convertDec rs (NewDec pos _ s q tys)        = NewDec pos (map convertType tys) s q tys
convertDec rs (FunDec pos _ _ s ss ps ty t) = FunDec pos undefined undefined s ss ps ty (runM (convertTerm t) const rs 0)
convertDec rs (SumDec pos s ss cs)          = SumDec pos s ss cs
convertDec rs (SubDec pos s q)              = SubDec pos s q

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

lookupConstructor :: [String] -> M ([String], [Type.Type], Type.Type)
lookupConstructor q = M (\ k r -> k (envStackLookupConstructor r q))

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
    BindTerm _ p t1 t2 -> do
      m <- gen
      p' <- convertPat p
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ BindTerm m p' t1' t2'
    CaseTerm _ t rs -> do
      m <- gen
      t' <- convertTerm t
      rs' <- mapM convertRule rs
      return $ CaseTerm m t' rs'
    ForTerm m1s m2 ps t1 t2 -> do
      m2' <- gen
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      case ps of
        Nothing ->
          return $ ForTerm m1s m2' Nothing t1' t2'
        Just ps -> do
          m1s' <- mapM (const gen) ps
          ps' <- mapM convertPat ps
          return $ ForTerm m1s' m2' (Just ps') t1' t2'
    SeqTerm t1 t2 -> do
      t1' <- convertTerm t1
      t2' <- convertTerm t2
      return $ SeqTerm t1' t2'
    StringTerm pos s -> do
      return $ StringTerm pos s
    TupleTerm pos _ ts -> do
      ms <- mapM gen1 ts
      ts' <- mapM convertTerm ts
      return $ TupleTerm pos ms ts'
    UnitTerm pos ->
      return $ UnitTerm pos
    UpperTerm pos _ _ s tas -> do
      (ss, ty) <- lookupFunction s
      ts' <- case tas of
        Nothing -> mapM gen1 ss
        Just tas -> return $ map convertType tas
      let ty' = Type.rename (zip ss ts') ty
      return $ UpperTerm pos ts' ty' s tas
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
    AscribePat pos p ty -> do
      p' <- convertPat p
      return $ AscribePat pos p' ty
    LowerPat pos s ->
      return $ LowerPat pos s
    TuplePat pos _ ps -> do
      m <- mapM gen1 ps
      ps' <- mapM convertPat ps
      return $ TuplePat pos m ps'
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
convertType (UpperTyp _ ["String"] _) = Type.String -- fix this
convertType (UpperTyp _ q tys) = Type.Variant q (map convertType tys)
-}
