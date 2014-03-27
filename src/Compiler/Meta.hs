module Compiler.Meta where

import Control.Applicative (Alternative, empty, (<|>))
import Control.Monad (liftM)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

tr :: Show a => a -> a
tr x = trace (show x) x

addMetavariables :: Syntax.Program -> Syntax.Program
addMetavariables p = run (programEnv p) $ updateProgram p

-- An environment is a direct path, the indirect path, the local type bindings,
-- and the declarations. The indifect path is the name of the environment
-- without accounting for new, so it is only different for units. We use the
-- indirect path to identify units which are primitives.
data Env = Env [Frame]
           deriving (Show)
type Frame = (Type.Path, Type.Path, [(String, Type.Type)], [Syntax.Dec])

programEnv :: Syntax.Program -> Env
programEnv (Syntax.Program decs) = Env [(Type.Path [], Type.Path [], [], decs)]

updateProgram ::  Syntax.Program -> M Syntax.Program
updateProgram (Syntax.Program decs) = do
  decs <- mapM updateDec decs
  return $ Syntax.Program decs

updateDec :: Syntax.Dec -> M Syntax.Dec
updateDec dec =
  case dec of
    Syntax.FunDec pos _ _ s vs ps ty t ->
      withEnvAddTypeParameters vs $ do
        tys' <- mapM convertPat ps
        ty' <- convertType ty
        t <- updateTerm t
        return $ Syntax.FunDec pos tys' ty' s vs ps ty t
    Syntax.ModDec pos s vs decs -> do
      n  <- return $ Type.Name s (map Type.Variable vs)
      q1 <- getEnvDirectPath
      q1 <- return $ Type.pathAddName q1 n
      q2 <- getEnvIndirectPath
      q2 <- return $ Type.pathAddName q2 n
      withEnvAddFrame (q1, q2, typeParameters vs, decs) $ do
        decs <- mapM updateDec decs
        return $ Syntax.ModDec pos s vs decs
    Syntax.NewDec pos _ s vs q -> do
      withEnvAddTypeParameters vs $ do
        q' <- convertPath q
        case q' of
          Type.Path [] -> unreachable "updateDec"
          Type.Path [n] ->
            inUnitWithName2 n $ do
              q' <- getEnvIndirectPath
              return $ Syntax.NewDec pos q' s vs q
          Type.Path (n:ns) -> do
            inModWithName n $ do
              Type.Path q' <- getEnvIndirectPath
              return $ Syntax.NewDec pos (Type.Path (q' ++ ns)) s vs q
    Syntax.SubDec pos _ s vs q ->
      withEnvAddTypeParameters vs $ do
        q' <- convertPath q
        inMod q' $ do
          q' <- getEnvIndirectPath
          return $ Syntax.SubDec pos q' s vs q
    Syntax.SumDec pos _ s vs cs -> do
      q <- getEnvIndirectPath
      let q' = Type.pathAddName q (Type.Name s (map Type.Variable vs))
      cs <- mapM updateConstructor cs
      return $ Syntax.SumDec pos q' s vs cs
    Syntax.UnitDec pos s vs decs -> do
      n  <- return $ Type.Name s (map Type.Variable vs)
      q1 <- getEnvDirectPath
      q1 <- return $ Type.pathAddName q1 n
      q2 <- getEnvIndirectPath
      q2 <- return $ Type.pathAddName q2 n
      withEnvAddFrame (q1, q2, typeParameters vs, decs) $ do
        decs <- mapM updateDec decs
        return $ Syntax.UnitDec pos s vs decs

updateConstructor :: (Syntax.Pos, [Type.Type], String, [Syntax.Type]) -> M (Syntax.Pos, [Type.Type], String, [Syntax.Type])
updateConstructor (pos, _, s, ty1s) = do
  ty2s <- mapM convertType ty1s
  return (pos, ty2s, s, ty1s)

updateTerm :: Syntax.Term -> M Syntax.Term
updateTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      ty <- gen
      t1 <- updateTerm t1
      t2 <- updateTerm t2
      return $ Syntax.ApplyTerm ty t1 t2
    Syntax.AscribeTerm pos _ t ty -> do
      ty' <- convertType ty
      t <- updateTerm t
      return $ Syntax.AscribeTerm pos ty' t ty
    Syntax.BindTerm _ p t1 t2 -> do
      ty <- gen
      p <- updatePat p
      t1 <- updateTerm t1
      t2 <- updateTerm t2
      return $ Syntax.BindTerm ty p t1 t2
    Syntax.CaseTerm _ t rs -> do
      ty <- gen
      t <- updateTerm t
      rs <- mapM updateRule rs
      return $ Syntax.CaseTerm ty t rs
    Syntax.SeqTerm t1 t2 -> do
      t1 <- updateTerm t1
      t2 <- updateTerm t2
      return $ Syntax.SeqTerm t1 t2
    Syntax.StringTerm pos x ->
      return $ Syntax.StringTerm pos x
    Syntax.UnitTerm pos ->
      return $ Syntax.UnitTerm pos
    Syntax.ForTerm _ _ ps t1 t2 -> do
      ty1s <- mapM (const gen) ps
      ty2 <- gen
      ps <- mapM updatePat ps
      t1 <- updateTerm t1
      t2 <- updateTerm t2
      return $ Syntax.ForTerm ty1s ty2 ps t1 t2
    Syntax.TupleTerm pos _ ts -> do
      tys <- mapM (const gen) ts
      ts <- mapM updateTerm ts
      return $ Syntax.TupleTerm pos tys ts
    Syntax.UpperTerm pos _ _ q ->
      case q of
        [(pos, "Continue", [])] ->
          return $ Syntax.UpperTerm pos (Type.Path [Type.Name "Continue" []])
                     (Type.Arrow (Type.Arrow Type.Unit (Type.Variant (Type.Path [Type.Name "Output" []])))
                                 (Type.Variant (Type.Path [Type.Name "Output" []])))
                     [(pos, "Continue", [])]
        [(pos, "Exit", [])] ->
          return $ Syntax.UpperTerm pos (Type.Path [Type.Name "Exit" []])
                     (Type.Variant (Type.Path [Type.Name "Output" []]))
                     [(pos, "Exit", [])]
        [(pos, "Write", [])] ->
          return $ Syntax.UpperTerm pos (Type.Path [Type.Name "Write" []])
                     (Type.Arrow Type.String
                                 (Type.Arrow (Type.Variant (Type.Path [Type.Name "Output" []]))
                                             (Type.Variant (Type.Path [Type.Name "Output" []]))))
                     [(pos, "Write", [])]
        [(pos, "Unreachable", tys)] -> do
          ty' <- case tys of
            [] -> gen
            [ty] -> convertType ty
            _ -> unreachable "updateTerm"
          return $ Syntax.UpperTerm pos (Type.Path [Type.Name "Unreachable" [ty']])
                     ty'
                     [(pos, "Unreachable", tys)]
        _ -> do
          -- _ <- trace ("3 " ++ show q) (return ())
          q' <- convertPath q
          -- _ <- trace ("4 " ++ show q') (return ())
          (q', ty') <- getFun q'
          -- _ <- trace ("5 " ++ show q') (return ())
          -- _ <- trace (show q') (return ())
          return $ Syntax.UpperTerm pos q' ty' q
    Syntax.VariableTerm pos x ->
      return $ Syntax.VariableTerm pos x

updateRule :: (Syntax.Pat, Syntax.Term) -> M (Syntax.Pat, Syntax.Term)
updateRule (p, t) = do
  p <- updatePat p
  t <- updateTerm t
  return (p, t)

updatePat :: Syntax.Pat -> M Syntax.Pat
updatePat p =
  case p of
    Syntax.AscribePat pos _ p ty -> do
      ty' <- convertType ty
      p <- updatePat p
      return $ Syntax.AscribePat pos ty' p ty
    Syntax.LowerPat pos x ->
      return $ Syntax.LowerPat pos x
    Syntax.TuplePat pos _ ps -> do
      tys <- mapM (const gen) ps
      return $ Syntax.TuplePat pos tys ps
    Syntax.UnderbarPat ->
      return Syntax.UnderbarPat
    Syntax.UnitPat pos ->
      return $ Syntax.UnitPat pos
    Syntax.UpperPat pos _ _ _ q ps -> do
      q' <- convertPath q
      (q', tys, ty) <- getCon q'
      ps <- mapM updatePat ps
      return $ Syntax.UpperPat pos q' tys ty q ps

-- The pattern must be fully typed to use this; i.e. function parameters.
-- Theoretically, getting an upper pat could require unification, so we don't
-- do it for now, although I think I could use the type checker module to do
-- it.
convertPat :: Syntax.Pat -> M Type.Type
convertPat p =
  case p of
    Syntax.AscribePat _ _ p ty -> convertType ty
    Syntax.LowerPat _ x -> unreachable "getPatType"
    Syntax.TuplePat _ _ ps -> liftM Type.Tuple (mapM convertPat ps)
    Syntax.UnderbarPat -> unreachable "getPatType"
    Syntax.UnitPat _ -> return $ Type.Unit
    Syntax.UpperPat _ _ _ _ q ps -> unreachable "getPatType"

convertType :: Syntax.Type -> M Type.Type
convertType ty = do
  case ty of
    Syntax.ArrowType ty1 ty2 -> do
      ty1 <- convertType ty1
      ty2 <- convertType ty2
      return $ Type.Arrow ty1 ty2
    Syntax.LowerType _ x ->
      lookupTypeVariable x
    Syntax.TupleType tys -> do
      tys <- mapM convertType tys
      return $ Type.Tuple tys
    Syntax.UnitType _ ->
      return $ Type.Unit
    Syntax.UpperType _ q -> do
      q <- convertPath q
      getSum q

-- Converts to a local Type.Path.
convertPath :: Syntax.Path -> M Type.Path
convertPath q = do
  ns <- mapM convertName q
  return $ Type.Path ns

convertName :: Syntax.Name -> M Type.Name
convertName (_, s, tys) = do
  tys <- mapM convertType tys
  return $ Type.Name s tys

getSum :: Type.Path -> M Type.Type
getSum (Type.Path ns) =
  case ns of
    [] ->
      unreachable "getSum"
    [n] ->
      getSumWithName n
    (n1:ns) -> do
      let (n2s, n3) = splitPath (Type.Path ns)
      inModWithName n1 $
        inResolveFields n2s $
          getSumWithField n3

getCon :: Type.Path -> M (Type.Path, [Type.Type], Type.Type)
getCon (Type.Path ns) =
  case ns of
    [] ->
      unreachable "getCon"
    [n] ->
      getConWithName n
    (n1:ns) -> do
      let (n2s, n3) = splitPath (Type.Path ns)
      inModWithName n1 $
        inResolveFields n2s $
          getConWithField n3

-- Returns the full path of the function as well as the type.
getFun :: Type.Path -> M (Type.Path, Type.Type)
getFun (Type.Path ns) =
  case ns of
    [] ->
      unreachable "getFun"
    [n] ->
      getFunWithName n
    (n1:ns) -> do
      let (n2s, n3) = splitPath (Type.Path ns)
      inModWithName n1 $
        inResolveFields n2s $
          getFunWithField n3

splitPath :: Type.Path -> ([Type.Name], Type.Name)
splitPath (Type.Path ns) =
  case reverse ns of
    [] -> unreachable "splitPath"
    (n:ns) -> (reverse ns, n)

inMod :: Type.Path -> M a -> M a
inMod (Type.Path ns) m =
  case ns of
    [] ->
      unreachable "inMod"
    (n:ns) ->
      inModWithName n $
        inResolveFields ns $
          m

inModWithName :: Type.Name -> M a -> M a
inModWithName n m = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n of
        _ ->
          unreachable $ "inModWithName 1: " ++ show n
    (x:xs) ->
      case x of
        (_, _ , _, decs) ->
          case search (hasModWithName n m) decs of
            Nothing -> withEnv (Env xs) (inModWithName n m)
            Just m -> m

inUnitWithName :: Type.Name -> Type.Path -> M a -> M a
inUnitWithName n1 q9 m = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n1 of
        Type.Name "Escape" [ty1, ty2] -> do
          withEnvAddFrame (Type.Path [Type.Name "Escape" [ty1, ty2]], q9, [], []) m
        _ -> unreachable $ "inUnitWithName: " ++ show n1
    (x:xs) ->
      case x of
        (_, _, _, decs) ->
          case search (hasUnitWithName n1 q9 m) decs of
            Nothing -> withEnv (Env xs) (inUnitWithName n1 q9 m)
            Just m -> m

inUnitWithName2 :: Type.Name -> M a -> M a
inUnitWithName2 n1 m = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n1 of
        Type.Name "Escape" [ty1, ty2] -> do
          withEnvAddFrame (Type.Path [Type.Name "Escape" [ty1, ty2]], Type.Path [Type.Name "Escape" [ty1, ty2]], [], []) m
        _ -> unreachable $ "inUnitWithName2: " ++ show n1
    (x:xs) ->
      case x of
        (_, _, _, decs) ->
          case search (hasUnitWithName2 n1 m) decs of
            Nothing -> withEnv (Env xs) (inUnitWithName2 n1 m)
            Just m -> m

inUnitWithField :: Type.Name -> Type.Path -> M a -> M a
inUnitWithField n1 q9 m = inUnitWithName n1 q9 m

inResolveFields :: [Type.Name] -> M a -> M a
inResolveFields ns m =
  case ns of
    [] -> m
    (n:ns) -> inResolveField n (inResolveFields ns m)

inResolveField :: Type.Name -> M a -> M a
inResolveField n m = inModWithName n m

getSumWithName :: Type.Name -> M Type.Type
getSumWithName n = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n of
        Type.Name "String" [] ->
          return Type.String
        Type.Name "Output" [] ->
          return $ Type.Variant (Type.Path [Type.Name "Output" []])
        _ ->
          unreachable "getSumWithName 2"
    (x:xs) ->
      case x of
        (_, _ , _, decs) ->
          case search (hasSumWithName n) decs of
            Nothing -> withEnv (Env xs) (getSumWithName n)
            Just m -> m

getConWithName :: Type.Name -> M (Type.Path, [Type.Type], Type.Type)
getConWithName n = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n of
        _ ->
          unreachable "getConWithName"
    (x:xs) ->
      case x of
        (_, _ , _, decs) ->
          case search (hasConWithName n) decs of
            Nothing -> withEnv (Env xs) (getConWithName n)
            Just m -> m

getFunWithName :: Type.Name -> M (Type.Path, Type.Type)
getFunWithName n = do
  Env xs <- getEnv
  case xs of
    [] ->
      case n of
        _ ->
          unreachable $ "getFunWithName 2: " ++ show n
    (x:xs) ->
      case x of
        (Type.Path [Type.Name "Escape" [ty1, ty2]], q, _, _) ->
          case n of
            Type.Name "Throw" [] -> do
              return (Type.pathAddName q n, Type.Arrow ty1 ty2)
            Type.Name "Catch" tys -> do
              ty3 <- case tys of
                [ty3] -> return ty3
                _ -> gen
              return (Type.pathAddName q (Type.Name "Catch" [ty3]),
                      Type.Arrow (Type.Arrow Type.Unit ty3)
                                 (Type.Arrow (Type.Arrow ty1
                                                         (Type.Arrow (Type.Arrow ty2
                                                                                 ty3)
                                                                     ty3))
                                             ty3))
            _ -> unreachable "getFunWithName Escape"
        (_, _ , _, decs) ->
          case search (hasFunWithName n) decs of
            Nothing -> withEnv (Env xs) (getFunWithName n)
            Just m -> m

hasModWithName :: Type.Name -> M a -> Syntax.Dec -> Maybe (M a)
hasModWithName (Type.Name s1 ty1s) m dec =
  case dec of
    Syntax.ModDec _ s2 vs decs | s1 == s2 -> Just $ do
      n  <- return $ Type.Name s1 ty1s
      q1 <- getEnvDirectPath
      q1 <- return $ Type.pathAddName q1 n
      q2 <- getEnvIndirectPath
      q2 <- return $ Type.pathAddName q2 n
      ty1s <- case ty1s of
        [] -> mapM (const gen) vs
        _ -> return ty1s
      withEnvAddFrame (q1, q2, zip vs ty1s, decs) m
    Syntax.NewDec _ _ s2 vs q2 | s1 == s2 -> Just $ do
      q3 <- getEnvIndirectPath
      ty1s <- case ty1s of
        [] -> mapM (const gen) vs
        _ -> return ty1s
      withEnvAddTypeVariables (zip vs ty1s) $ do
        q2 <- convertPath q2
        inUnit q2 (Type.pathAddName q3 (Type.Name s1 ty1s)) m
    _ -> Nothing

hasUnitWithName :: Type.Name -> Type.Path -> M a -> Syntax.Dec -> Maybe (M a)
hasUnitWithName (Type.Name s1 ty1s) q9 m dec =
  case dec of
    Syntax.UnitDec _ s2 vs decs | s1 == s2 -> Just $ do
      q1 <- getEnvDirectPath
      ty1s <- case ty1s of
        [] -> mapM (const gen) vs
        _ -> return ty1s
      withEnvAddFrame (Type.pathAddName q1 (Type.Name s1 ty1s), q9, zip vs ty1s, decs) m
    _ -> Nothing

hasUnitWithName2 :: Type.Name -> M a -> Syntax.Dec -> Maybe (M a)
hasUnitWithName2 (Type.Name s1 ty1s) m dec =
  case dec of
    Syntax.UnitDec _ s2 vs decs | s1 == s2 -> Just $ do
      ty1s <- case ty1s of
        [] -> mapM (const gen) vs
        _ -> return ty1s
      n  <- return $ Type.Name s1 ty1s
      q1 <- getEnvDirectPath
      q1 <- return $ Type.pathAddName q1 n
      q2 <- getEnvIndirectPath
      q2 <- return $ Type.pathAddName q2 n
      withEnvAddFrame (q1, q2, zip vs ty1s, decs) m
    _ -> Nothing


-- The second path is used to give a name to the new instance.
inUnit :: Type.Path -> Type.Path -> M a -> M a
inUnit (Type.Path ns) q9 m =
  case ns of
    [] -> unreachable "inUnit"
    [n1] -> inUnitWithName n1 q9 m
    (n1:ns) -> do
      let (n2s, n3) = splitPath (Type.Path ns)
      inModWithName n1 $
        inResolveFields n2s $
          inUnitWithField n3 q9 m

hasSumWithName :: Type.Name -> Syntax.Dec -> Maybe (M Type.Type)
hasSumWithName (Type.Name s1 ty1s) dec =
  case dec of
    Syntax.SumDec _ _ s2 _ _ | s1 == s2 -> Just $ do
      q <- getEnvIndirectPath
      return $ Type.Variant (Type.pathAddName q (Type.Name s1 ty1s))
    _ -> Nothing

hasConWithName :: Type.Name -> Syntax.Dec -> Maybe (M (Type.Path, [Type.Type], Type.Type))
hasConWithName (Type.Name s1 ty1s) dec =
  case dec of
    Syntax.SumDec _ _ s2 vs cs ->
      let has (_, _, s3, ty2s) | s1 == s3 = Just $ do
            q <- getEnvIndirectPath
            ty1s <- case ty1s of
              [] -> mapM (const gen) vs
              _ -> return ty1s
            withEnvAddTypeVariables (zip vs ty1s) $ do
              ty2s <- mapM convertType ty2s
              let q2 = Type.pathAddName q (Type.Name s2 ty1s)
              let ty2 = Type.Variant q2
              return (Type.pathAddName q (Type.Name s3 ty1s), ty2s, ty2)
          has _ = Nothing
       in search has cs
    _ -> Nothing

hasFunWithName :: Type.Name -> Syntax.Dec -> Maybe (M (Type.Path, Type.Type))
hasFunWithName (Type.Name s1 ty1s) dec =
  case dec of
    Syntax.SumDec _ _ s2 vs cs ->
      let has (_, _, s3, ty2s) | s1 == s3 = Just $ do
            q <- getEnvIndirectPath
            ty1s <- case ty1s of
              [] -> mapM (const gen) vs
              _ -> return ty1s
            withEnvAddTypeVariables (zip vs ty1s) $ do
              ty2s <- mapM convertType ty2s
              let q2 = Type.pathAddName q (Type.Name s2 ty1s)
              let ty2 = Type.Variant q2
              return (Type.pathAddName q (Type.Name s3 ty1s), foldr Type.Arrow ty2 ty2s)
          has _ = Nothing
       in search has cs
    Syntax.FunDec _ _ _ s2 vs pats ty _ | s1 == s2 -> Just $ do
      q <- getEnvIndirectPath
      -- _ <- trace ("6 " ++ show q) (return ())
      ty1s <- case ty1s of
        [] -> mapM (const gen) vs
        _ -> return ty1s
      withEnvAddTypeVariables (zip vs ty1s) $ do
        ty2s <- mapM convertPat pats
        ty2 <- convertType ty
        return (Type.pathAddName q (Type.Name s1 ty1s), foldr Type.Arrow ty2 ty2s)
    _ -> Nothing

getSumWithField :: Type.Name -> M Type.Type
getSumWithField n = getSumWithName n

getConWithField :: Type.Name -> M (Type.Path, [Type.Type], Type.Type)
getConWithField n = getConWithName n

getFunWithField :: Type.Name -> M (Type.Path, Type.Type)
getFunWithField n = getFunWithName n

lookupTypeVariable :: String -> M Type.Type
lookupTypeVariable s = do
  Env r <- getEnv
  return $ fromMaybe (unreachable $ "lookupTypeVariable: " ++ s) (search has r)
  where has (_, _, xs, _) = lookup s xs

getEnvDirectPath :: M Type.Path
getEnvDirectPath = do
  Env r <- getEnv
  case r of
    [] -> unreachable "getEnvDirectPath"
    ((q, _, _, _) : _) -> return q

getEnvIndirectPath :: M Type.Path
getEnvIndirectPath = do
  Env r <- getEnv
  case r of
    [] -> unreachable "getEnvIndirectPath"
    ((_, q, _, _) : _) -> return q

withEnvAddFrame :: Frame -> M a -> M a
withEnvAddFrame x m = do
  Env r <- getEnv
  withEnv (Env (x : r)) m

withEnvAddTypeParameters :: [String] -> M a -> M a
withEnvAddTypeParameters vs m = do
  withEnvAddTypeVariables (typeParameters vs) m

withEnvAddTypeVariables :: [(String, Type.Type)] -> M a -> M a
withEnvAddTypeVariables xs m = do
  q1 <- getEnvDirectPath
  q2 <- getEnvIndirectPath
  withEnvAddFrame (q1, q2, xs, []) m

typeParameters :: [String] -> [(String, Type.Type)]
typeParameters vs = map (\ v -> (v, Type.Variable v)) vs

run :: Env -> M Syntax.Program -> Syntax.Program
run r m =  runM m r k 0
  where k x _ = x

newtype M a = M { runM :: Env -> (a -> Int -> Syntax.Program) -> Int -> Syntax.Program }

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


-- Utility Functions

search :: Alternative m => (a -> m b) -> [a] -> m b
search f = choice . map f
-- search f [] = empty
-- search f (x:xs) = search f xs <|> f x -- maybe (search f xs) Just (f x)

choice :: Alternative m => [m a] -> m a
choice []     = empty
choice (x:xs) = x <|> choice xs

todo :: String -> a
todo s = error $ "todo: Meta." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Meta." ++ s
