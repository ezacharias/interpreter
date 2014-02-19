module Compiler.Elaborator where

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.IntMap as IdentMap

import qualified Compiler.Syntax as Syntax
import qualified Compiler.Simple as Simple
import qualified Compiler.Type as Type

type IdentMap = IdentMap.IntMap

elaborate :: Syntax.Program -> Simple.Program
elaborate p = run p $ do
  d <- getFun (Type.Path [(Type.Name "Main" [])])
  finish
  x1 <- getProgramTags
  x2 <- getProgramSums
  x3 <- getProgramFuns
  return $ Simple.Program x1 x2 x3 d

getFun :: Type.Path -> M Simple.Ident
getFun q = do
  r <- getEnv
  (q, f) <- return $ envGetFun r q
  x <- getExportedFuns
  case Map.lookup q x of
    Nothing -> do
      d <- gen
      setExportedFuns (Map.insert q d x)
      addWork (f d)
      return d
    Just d -> return d

envGetFun :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetFun r (Type.Path [n])    = envGetFunWithName r n
envGetFun r (Type.Path (n:ns)) = envGetFunWithFields (envGetModWithName r n) (Type.Path ns)
envGetFun r (Type.Path [])     = unreachable "envGetFun"

envGetFunWithFields :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetFunWithFields (Env []) _ = unreachable "envGetFunWithFields"
envGetFunWithFields _ (Type.Path []) = unreachable "envGetFunWithFields"
envGetFunWithFields (r@(Env ((b, Type.Path q, _, ds):r'))) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps _ t | s1 == s2 ->
              let q' = q ++ [Type.Name s1 tys]
                  f d = withEnv r $ do
                    t <- elaborateLambda ps (todo "envGetFunWithFields") t
                    ty0s <- mapM elaborateType ty0s
                    ty0 <- elaborateType ty0
                    ty <- return $ foldr Simple.ArrowType ty0 ty0s
                    addFun d (Simple.Fun ty t)
               in Just (Type.Path q', f)
            _ ->
              Nothing
envGetFunWithFields (Env r@((b, Type.Path q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields"
        check (Just r'') = envGetFunWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.Path (q ++ [Type.Name s1 tys]), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              let q' = let f [] = unreachable "envGetFunWithFields"
                           f [s3] = [Type.Name s3 ty2s]
                           f (s3:s3s) = (Type.Name s3 []) : f s3s
                        in f s3s
               in Just (envGetUnit (Env r) (Type.Path q') (Type.Path (q ++ [Type.Name s1 tys])))
            _ ->
              Nothing

getSum :: Type.Path -> M Simple.Ident
getSum q = do
  r <- getEnv
  (q, f) <- return $ envGetSum r q
  x <- getExportedSums
  case Map.lookup q x of
    Nothing -> do
      d <- gen
      setExportedSums (Map.insert q d x)
      addWork (f d)
      return d
    Just d -> return d

envGetSum :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetSum r (Type.Path [n])    = envGetSumWithName r n
envGetSum r (Type.Path (n:ns)) = envGetSumWithFields (envGetModWithName r n) (Type.Path ns)
envGetSum r (Type.Path [])     = unreachable "envGetSum"

primitiveOutput :: Simple.Ident -> M ()
primitiveOutput d =
  addSum d $ Simple.Sum [[]]

envGetSumWithName :: Env -> Type.Name -> (Type.Path, Simple.Ident -> M ())
envGetSumWithName (Env []) (Type.Name "Output" []) = (Type.Path [Type.Name "Output" []], primitiveOutput)
envGetSumWithName (Env []) n = unreachable $ "envGetSumWithName: " ++ show n
envGetSumWithName (Env r@((b, Type.Path q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetSumWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.SumDec _ s2 _ _ | s1 == s2 ->
              let q' = todo "envGetSumWithName"
                  f = todo "envGetSumWithName"
               in Just (q', f)
            _ -> Nothing

            {-
          SumDec Pos String [String] [(Pos, String, [Typ])]

          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps _ t | s1 == s2 ->
              let q' = Type.Path (q ++ [Type.Name s1 tys])
                  f d = withEnv (Env r) $ do
                    t <- elaborateLambda ps (map (const (todo "envGetFunWithName 1")) ps) t
                    ty0s <- mapM elaborateType ty0s
                    ty0 <- elaborateType ty0
                    ty <- return $ foldr Simple.ArrowType ty0 ty0s
                    addFun d (Simple.Fun ty t)
               in Just (q', f)
            _ ->
              Nothing
            -}


envGetSumWithFields :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetSumWithFields = todo "envGetSumWithFields"

-- The second path is the full name of the new instance.
envGetUnit :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnit _ (Type.Path [])     = unreachable "envGetUnit"
envGetUnit r (Type.Path [n])    = envGetUnitWithName r n
envGetUnit r (Type.Path (n:ns)) = envGetUnitWithFields (envGetModWithName r n) (Type.Path ns)

envGetUnitWithName :: Env -> Type.Name -> (Type.Path -> Env)
envGetUnitWithName (Env []) _ = unreachable "envGetUnitWithName"
envGetUnitWithName (Env r@((b, Type.Path q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetUnitWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              Just (\ q' -> Env ((Just (Type.Path (q ++ [Type.Name s1 tys])), q', zip s3s tys, ds) : r))
            _ ->
              Nothing

envGetUnitWithFields :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnitWithFields (Env []) _ = unreachable "envGetUnitWithFields"
envGetUnitWithFields _ (Type.Path []) = unreachable "envGetUnitWithFields"
envGetUnitWithFields (Env r@((b, Type.Path q, _, ds):r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              Just (\ q' -> Env ((Just (Type.Path (q ++ [Type.Name s1 tys])), q', zip s3s tys, ds) : r))
            _ ->
              Nothing
envGetUnitWithFields (Env r@((b, Type.Path q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just r'') = envGetUnitWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.Path (q ++ [Type.Name s1 tys]), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              let q' = let f [] = unreachable "envGetUnitWithFields"
                           f [s3] = [Type.Name s3 ty2s]
                           f (s3:s3s) = (Type.Name s3 []) : f s3s
                        in f s3s
               in Just (envGetUnit (Env r) (Type.Path q') (Type.Path (q ++ [Type.Name s1 tys])))
            _ ->
              Nothing

envGetMod :: Env -> Type.Path -> Env
envGetMod r (Type.Path q) =
  case q of
    [] -> unreachable "envGetMod"
    n:ns -> envGetModWithFields (envGetModWithName r n) (Type.Path ns)

envGetModWithFields :: Env -> Type.Path -> Env
envGetModWithFields (Env []) _ = unreachable "envGetModWithFields"
envGetModWithFields r (Type.Path []) = r
envGetModWithFields (Env r@((b, Type.Path q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetMod"
        check (Just r'') = envGetModWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.Path (q ++ [Type.Name s1 tys]), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              let q' = let f [] = unreachable "envGetModWithFields"
                           f [s3] = [Type.Name s3 ty2s]
                           f (s3:s3s) = (Type.Name s3 []) : f s3s
                        in f s3s
               in Just (envGetUnit (Env r) (Type.Path q') (Type.Path (q ++ [Type.Name s1 tys])))
            _ ->
              Nothing

envGetModWithName :: Env -> Type.Name -> Env
envGetModWithName (Env []) _ = unreachable "envGetModWithName"
envGetModWithName (Env r@((b, Type.Path q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetModWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.Path (q ++ [Type.Name s1 []]) , [], ds) : r))
            Syntax.SubDec _ s2 q2 | s1 == s2 ->
              let q2' = map (\ s -> (Type.Name s [])) q2
                  -- Note that r' is used because alias lookup starts at the outer level.
               in Just (envGetMod (Env r') (Type.Path q2'))
            _ ->
              Nothing

primitiveExit :: Int -> M ()
primitiveExit d =
  addFun d $ Simple.Fun (Simple.SumType 0) (Simple.ConstructorTerm 0 0 [])

envGetFunWithName :: Env -> Type.Name -> (Type.Path, Simple.Ident -> M ())
envGetFunWithName (Env []) (Type.Name "Exit" []) = (Type.Path [Type.Name "Exit" []], primitiveExit)
envGetFunWithName (Env []) n = unreachable $ "envGetFunWithName: " ++ show n
envGetFunWithName (Env r@((b, Type.Path q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetFunWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps _ t | s1 == s2 ->
              let q' = Type.Path (q ++ [Type.Name s1 tys])
                  f d = withEnv (Env r) $ do
                    t <- elaborateLambda ps (map (const (todo "envGetFunWithName 1")) ps) t
                    ty0s <- mapM elaborateType ty0s
                    ty0 <- elaborateType ty0
                    ty <- return $ foldr Simple.ArrowType ty0 ty0s
                    addFun d (Simple.Fun ty t)
               in Just (q', f)
            _ ->
              Nothing

elaborateLambda :: [Syntax.Pat] -> [Type.Type] -> Syntax.Term -> M Simple.Term
elaborateLambda []     []       t = elaborateTerm t
elaborateLambda (p:ps) (ty:tys) t = do
  d <- gen
  withPat d p $ do
    t <- elaborateLambda ps tys t
    ty <- elaborateType ty
    return $ Simple.LambdaTerm d ty t
elaborateLambda _ _ _ = unreachable "elaborateLambda"

elaborateType :: Type.Type -> M Simple.Type
elaborateType ty =
  case ty of
    Type.Arrow ty1 ty2 -> do
      ty1 <- elaborateType ty1
      ty2 <- elaborateType ty2
      return $ Simple.ArrowType ty1 ty2
    Type.Metavariable _ ->
      unreachable "elaborateType"
    Type.String ->
      return $ Simple.StringType
    Type.Tuple tys -> do
      tys <- mapM elaborateType tys
      return $ Simple.TupleType tys
    Type.Unit ->
       return $ Simple.UnitType
    Type.Variable x -> do
      ty <- getLowerType x
      elaborateType ty
    Type.Variant q -> do
      d <- getSum q
      return $ Simple.SumType d

-- Resolves any type variables in the path and handles units.
updatePath :: Type.Path -> M Type.Path
updatePath q = do
  ns <- mapM updateName (Type.pathNames q)
  r <- getEnv
  return $ envUnitPath r (Type.Path ns)

envUnitPath :: Env -> Type.Path -> Type.Path
envUnitPath (Env r) q1 = check $ search f r
  where check Nothing  = q1
        check (Just x) = x
        f (Nothing, q3, _, _) = Nothing
        f (Just q2, q3, _, _) = tryUnitPath q1 q2 q3

-- If the second path matches the start of the third, add the first path to the start of the third.
tryUnitPath :: Type.Path -> Type.Path -> Type.Path -> Maybe Type.Path
tryUnitPath (Type.Path q1) (Type.Path []) (Type.Path q3) = Just (Type.Path (q1 ++ q3))
tryUnitPath (Type.Path (n1:n1s)) (Type.Path (n2:n2s)) q3 | n1 == n2 = tryUnitPath (Type.Path n1s) (Type.Path n2s) q3
tryUnitPath _ _ _ = Nothing

updateName :: Type.Name -> M Type.Name
updateName (Type.Name s tys) = do
  tys <- mapM updateType tys
  return $ Type.Name s tys

updateType :: Type.Type -> M Type.Type
updateType ty =
  case ty of
    Type.Arrow ty1 ty2 -> do
      ty1 <- updateType ty1
      ty2 <- updateType ty2
      return $ Type.Arrow ty1 ty2
    Type.Metavariable _ ->
      unreachable "updateType"
    Type.String ->
      return $ Type.String
    Type.Tuple tys -> do
      tys <- mapM updateType tys
      return $ Type.Tuple tys
    Type.Unit ->
       return $ Type.Unit
    Type.Variable x ->
      getLowerType x
    Type.Variant q -> do
      q <- updatePath q
      return $ Type.Variant q

-- Lookup up the type in the environment.
getLowerType :: String -> M Type.Type
getLowerType = todo "getLowerType"

-- This only works for singleton constructors.
withPat :: Simple.Ident -> Syntax.Pat -> M Simple.Term -> M Simple.Term
withPat d pat  m=
  case pat of
    Syntax.AscribePat _ p _ ->
      withPat d p m
    Syntax.LowerPat _ s ->
      withLowerBind s d m
    Syntax.TuplePat _ _ ps -> do
      ds <- mapM (const gen) ps
      t <- withPats ds ps m
      return $ Simple.UntupleTerm ds (Simple.VariableTerm d) t
    Syntax.UnderbarPat ->
      m
    Syntax.UnitPat _ ->
      m
    Syntax.UpperPat _ _ _ _ ps -> do
      ds <- mapM (const gen) ps
      t <- withPats ds ps m
      return $ Simple.CaseTerm (Simple.VariableTerm d) [(ds, t)]

withPats :: [Simple.Ident] -> [Syntax.Pat] -> M Simple.Term -> M Simple.Term
withPats [] [] m = m
withPats (d:ds) (p:ps) m = withPat d p (withPats ds ps m)
withPats _ _ _ = unreachable "withPats"

-- This does not, from what I can see, require a type.
withLowerBind :: String -> Simple.Ident -> M Simple.Term -> M Simple.Term
withLowerBind = todo "withLowerBind"

elaborateTerm :: Syntax.Term -> M Simple.Term
elaborateTerm t =
  case t of
    Syntax.CaseTerm _ t rs -> do
      t <- elaborateTerm t
      elaborateCase t rs
--    Syntax.UpperTerm _ [] _ ["Exit"] Nothing ->
    Syntax.UpperTerm _ tys _ ss _ -> do
      d <- getFun (convertQual ss tys)
      return $ Simple.FunTerm d
    _ -> todo $ "elaborateTerm: " ++ show t

convertQual :: [String] -> [Type.Type] -> Type.Path
convertQual ss tys = Type.Path (f ss)
  where f [] = unreachable "convertQual"
        f [s] = [Type.Name s tys]
        f (s:ss) = Type.Name s [] : f ss

elaborateCase :: Simple.Term -> [Syntax.Rule] -> M Simple.Term
elaborateCase t1 [] = unreachable "elaborateCase"
elaborateCase t1 [(p, t2)] = elaborateBind p t1 (elaborateTerm t2)
elaborateCase t1 rs = todo "elaborateCase"

elaborateBind :: Syntax.Pat -> Simple.Term -> M Simple.Term -> M Simple.Term
elaborateBind = todo "elaborateBind"

-- An environment is the full path, the local type bindings, and the declarations.
data Env = Env [(Maybe Type.Path, Type.Path, [(String, Type.Type)], [Syntax.Dec])]

run :: Syntax.Program -> M Simple.Program -> Simple.Program
run (Syntax.Program ds) m = runM m r k genVal [] exportedSums exportedFuns programTags programSums programFuns
  where r = Env [(Nothing, Type.Path [], [], ds)]
        k x _ _ _ _ _ _ _ = x
        genVal = 2
        exportedSums = Map.empty
        exportedFuns = Map.empty
        programTags = IdentMap.empty
        programSums = IdentMap.fromList [ (0, Simple.Sum [[]])
                                        ]
        programFuns = IdentMap.fromList [ (1, Simple.Fun (todo "run") (Simple.ConstructorTerm 0 0 []))
                                        ]

newtype M a = M { runM :: Env -> (a -> Int -> [M ()] -> Map Type.Path Int -> Map Type.Path Int -> Simple.IdentMap Simple.Tag -> Simple.IdentMap Simple.Sum -> Simple.IdentMap Simple.Fun -> Simple.Program)
                                    -> Int -> [M ()] -> Map Type.Path Int -> Map Type.Path Int -> Simple.IdentMap Simple.Tag -> Simple.IdentMap Simple.Sum -> Simple.IdentMap Simple.Fun -> Simple.Program
                }

instance Monad M where
  return x = M (\ r k -> k x)
  m >>= f = M (\ r k -> runM m r (\ x -> runM (f x) r k))

getEnv :: M Env
getEnv = M f
  where f r k = k r

withEnv :: Env -> M () -> M ()
withEnv r' m = M f
  where f r k = runM m r' k

getExportedFuns :: M (Map Type.Path Int)
getExportedFuns = M f
  where f r k genVal work exportedSums exportedFuns = k exportedFuns genVal work exportedSums exportedFuns

setExportedFuns :: Map Type.Path Int -> M ()
setExportedFuns exportedFuns' = M f
  where f r k genVal work exportedSums exportedFuns = k () genVal work exportedSums exportedFuns'

getExportedSums :: M (Map Type.Path Int)
getExportedSums = M f
  where f r k genVal work exportedSums exportedFuns = k exportedSums genVal work exportedSums exportedFuns

setExportedSums :: Map Type.Path Int -> M ()
setExportedSums exportedSums' = M f
  where f r k genVal work exportedSums exportedFuns = k () genVal work exportedSums' exportedFuns

gen :: M Simple.Ident
gen = M f
  where f r k genVal work exportedFuns = k genVal (genVal + 1) work exportedFuns

getWork :: M [M ()]
getWork = M f
  where f r k genVal work exportedFuns = k work genVal work exportedFuns

setWork :: [M ()] -> M ()
setWork work' = M f
  where f r k genVal work exportedFuns = k () genVal work' exportedFuns

addWork :: M () -> M ()
addWork m = do
  work <- getWork
  setWork (m : work)

finish :: M ()
finish = do
  work <- getWork
  case work of
    [] ->
      return ()
    (m : work) -> do
      setWork work
      m
      finish

addFun :: Simple.Ident -> Simple.Fun -> M ()
addFun d x = M f
  where f r k genVal work exportedSums exportedFuns programTags programSums programFuns =
         k () genVal work exportedSums exportedFuns programTags programSums (IdentMap.insert d x programFuns)

addSum :: Simple.Ident -> Simple.Sum -> M ()
addSum d x = M f
  where f r k genVal work exportedSums exportedFuns programTags programSums programFuns =
         k () genVal work exportedSums exportedFuns programTags (IdentMap.insert d x programSums) programFuns

getProgramTags :: M (Simple.IdentMap Simple.Tag)
getProgramTags = M f
  where f r k genVal work exportedSums exportedFuns programTags programSums programFuns =
         k programTags genVal work exportedSums exportedFuns programTags programSums programFuns

getProgramSums :: M (Simple.IdentMap Simple.Sum)
getProgramSums = M f
  where f r k genVal work exportedSums exportedFuns programTags programSums programFuns =
         k programSums genVal work exportedSums exportedFuns programTags programSums programFuns

getProgramFuns :: M (Simple.IdentMap Simple.Fun)
getProgramFuns = M f
  where f r k genVal work exportedSums exportedFuns programTags programSums programFuns =
         k programFuns genVal work exportedSums exportedFuns programTags programSums programFuns

-- Utility Functions

search :: (a -> Maybe b) -> [a] -> Maybe b
search f [] = Nothing
search f (x:xs) = maybe (search f xs) Just (f x)

todo :: String -> a
todo s = error $ "todo: Elaborator." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Elaborator." ++ s

{-
type M a = [a]

data Path = Path Name [Field]
data Full = Full [Field]

data Name  = Name String [Simple.Type]
data Field = Field String [Simple.Type]

-- An environment is the full path, the local type bindings, and the declarations.
type Env = [(Full, [(String, Simple.Type)], [Syntax.Dec])]

elaborateTerm :: Syntax.Term -> M Simple.Term
elaborateTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      return $ Simple.ApplyTerm t1 t2
    Syntax.AscribeTerm _ t _ ->
      elaborateTerm t
    Syntax.BindTerm _ p t1 t2 ->
      undefined
    Syntax.CaseTerm ty t rs -> do
      ty <- elaborateType ty
      t <- elaborateTerm t
      elaborateRules ty t (map (\ (p, t) -> (p, elaborateTerm t)) rs)
    Syntax.ForTerm _ _ Nothing t1 t2 -> do
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      d <- gen
      let t3 = Simple.LambdaTerm d Simple.UnitType t2
      return $ Simple.ApplyTerm t1 t3
    Syntax.ForTerm _ _ (Just ps) t1 t2 -> do
      t1 <- elaborateTerm t1
      t3 <- elaborateLambda ps t2
      d <- gen
      return $ Simple.ApplyTerm t1 t3
    Syntax.SeqTerm t1 t2 -> do
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      d <- gen
      return $ Simple.BindTerm d t1 t2
    Syntax.StringTerm _ x ->
      return $ Simple.StringTerm x
    Syntax.TupleTerm _ _ ts -> do
      ts <- mapM elaborateTerm ts
      return $ Simple.TupleTerm ts
    Syntax.UnitTerm _ ->
      return Simple.UnitTerm
    Syntax.UpperTerm _ tys _ q _ -> do
      tys <- map elaborateType tys
      q <- getFunFullWithPath (tempFix q tys)
      d <- getFunIdentWithFull q
      return $ Simple.FunTerm d
    Syntax.VariableTerm _ d -> do
      d <- getLower d
      return $ Simple.VariableTerm d

getFunIdentWithFull :: Full -> M Simple.Ident
getFunIdentWithFull = undefined

getFunFullWithPath :: Path -> M Full
getFunFullWithPath q = do
  r <- getEnv
  return $ envGetFunFullWithPath r q

envGetFunFullWithPath :: Env -> Path -> Full
envGetFunFullWithPath r (Path n []) = envGetFunFullWithName r n
envGetFunFullWithPath r (Path n q) = undefined (envGetEnvWithName r n)

envGetFunFullWithName :: Env -> Name -> Full
envGetFunFullWithName r n = fromMaybe (unreachable "envGetFullWithName") (search f r)
  where f (q, _, ds) = find (hasFun n) ds >>= const (Just (fullAppendName q n))

-- Should alse check constructors.
hasFun :: Name -> Syntax.Dec -> Bool
hasFun (Name s1 tys) (Syntax.FunDec _ s2 _ _ _ _) | s1 == s2  = True
hasFun _ _ = False

fullAppendName :: Full -> Name -> Full
fullAppendName q (Name s tys) = fullAppendField q (Field s tys)

fullAppendField :: Full -> Field -> Full
fullAppendField (Full q) n = Full (q ++ [n])

envGetEnvWithName :: Env -> Name -> Env
envGetEnvWithName []                n = unreachable "envGetEnvWithName"
envGetEnvWithName ((q, bs, ds) : r) n = fromMaybe (envGetEnvWithName r n) (search f ds)
  where f d = let (Name s tys) = n
               in case d of
                    Syntax.ModDec _ s' ds'  | s == s' -> Just ((fullAppendName q n, [], ds') : (q, bs, ds) : r)
                    Syntax.NewDec _ s' q' _ | s == s' -> undefined
                    Syntax.SubDec _ s' q'   | s == s' -> Just (envGetEnvWithPath r (tempFix q' []))
                    _ -> Nothing

envGetEnvWithPath :: Env -> Path -> Env
envGetEnvWithPath r (Path n q) = foldl envGetEnvWithField (envGetEnvWithName r n) q

envGetEnvWithField :: Env -> Field -> Env
envGetEnvWithField [] _ = unreachable "envGetEnvWithField"
envGetEnvWithField ((q, bs, ds) : r) n = fromMaybe (unreachable "envGetEnvWithField") (search f ds)
  where f d = let (Field s tys) = n
               in case d of
                    Syntax.ModDec _ s' ds'  | s == s' -> Just ((fullAppendField q n, [], ds') : (q, bs, ds) : r)
                    Syntax.NewDec _ s' q' _ | s == s' -> Just (envWithNew ((q, bs, ds) : r) (fullAppendField q n) (tempFix q' undefined))
                    Syntax.SubDec _ s' q'   | s == s' -> unreachable "envGetEnvWithField"
                    _ -> Nothing

-- We need to lookup the unit and modify the full path.
envWithNew :: Env -> Full -> Path -> Env
envWithNew r q' (Path n []) = envNewWithName r q' n
envWithNew r q' (Path n q)  = let (r', n') = envGetPairWithFields (envGetEnvWithName r n) q
                               in envNewWithField r' q' n'

envNewWithName :: Env -> Full -> Name -> Env
envNewWithName [] _ _ = unreachable "envNewWithName"
envNewWithName ((q, bs, ds) : r) q' n = fromMaybe (envNewWithName r q' n) (search f ds)
  where f d = let (Name s tys) = n
               in case d of
                    Syntax.UnitDec _ s' tys' ds' | s == s' -> Just ((q', undefined, ds') : (q, bs, ds) : r)
                    _ -> Nothing

envNewWithField :: Env -> Full -> Field -> Env
envNewWithField [] _ _ = unreachable "envNewWithField"
envNewWithField ((q, bs, ds) : r) q' n = fromMaybe (unreachable "envNewWithField") (search f ds)
  where f d = let (Field s tys) = n
               in case d of
                    Syntax.UnitDec _ s' bs' ds' | s == s' -> Just ((q', zip bs' tys, ds') : (q, bs, ds) : r)
                    _ -> Nothing

envGetPairWithFields :: Env -> [Field] -> (Env, Field)
envGetPairWithFields r []     = unreachable "envGetPairWithFields"
envGetPairWithFields r [x]    = (r, x)
envGetPairWithFields r (x:xs) = envGetPairWithFields (envGetEnvWithField r x) xs

-}

{-

-- Looks up the internal module name and returns the environment.
envGet :: Env -> Name -> Env
envGet = undefined

envGetFun :: Env -> Name -> Qual
envGetFun [] _ = unreachable "envGetFun"
envGetFun ((q, ds):r) n = maybe (envGetFun r n) (const $ q ++ [n]) (find (hasFun n) ds)

-- We first get the module. We then resolve the path. We are actually then done because we know the function is there.
envResolveFun :: Env -> Qual -> Qual
envResolveFun r [] = unreachable "envResolveFun"
envResolveFun r [n] = envGetFun r n
envResolveFun r (n : q) = envPath (envGetWithPath r (n : dropLast q)) ++ last q

envPath :: Env -> Qual
envPath (q, _) = q
-}

{-
-- Returns the path.
envResolve :: Env -> Qual -> Env
envResolve r [] = r
envResolve r (n:q) = envResolve (envModuleField r n) q

envModuleField :: Env -> Name -> Env
envModuleField [] _ = unreachable "envModuleField"
envModuleField ((s,ds):r) n =
  let d = fromMaybe (unreachable "envModuleField") (find (hasModField n) ds)
   in case d of
        Syntax.ModDec _ s' ds' -> (s', ds') : (s, ds) : r
        Syntax.NewDec _ s' q' _ -> undefined
        _ -> unreachable "envModuleField"

-- Not aliases because aliases do not create fields.
hasModField :: Name -> Syntax.Dec -> Bool
hasModField (s1, tys) (Syntax.ModDec _ s2 _) | s1 == s2 = True
hasModField (s1, tys) (Syntax.NewDec _ s2 _ _) | s1 == s2 = True
hasModField _ _ = False

envPath :: Env -> Qual
envPath [] = []
envPath ((s, _) : r) = (s, []) : envPath r

-}

{-
-- This simply converts Syntax.Qual to Qual.
tempFix :: Syntax.Qual -> [Simple.Type] -> Path
tempFix [] tys     = unreachable "tempFix"
tempFix [s]    tys = Path (Name s tys) []
tempFix (s:ss) tys = Path (Name s []) (tempFixFields ss tys)

tempFixFields :: Syntax.Qual -> [Simple.Type] -> [Field]
tempFixFields []     tys = []
tempFixFields [s]    tys = [Field s tys]
tempFixFields (s:ss) tys = Field s [] : tempFixFields ss tys

elaborateType :: Type.Type -> M Simple.Type
elaborateType = undefined

elaborateRules :: Simple.Type -> Simple.Term -> [(Syntax.Pat, M Simple.Term)] -> M Simple.Term
elaborateRules = undefined

getLower :: String -> M Simple.Ident
getLower = undefined
-}

{-

type Qual = [(String, [Simple.Type])]

finish :: M ()
finish = do
  ms <- getWork
  case ms of
    [] ->
      return ()
    (m:ms) -> do
      setWork ms
      m
      finish

-- This uses a fully qualified name. First we check to see if the function has
-- already been exported. If not, we export it.
getFun :: Qual -> M Simple.Ident
getFun q = do
  x <- getExportedFuns
  case Map.lookup q x of
    Nothing -> do
      d <- gen
      setExportedFuns (Map.insert q (d, Nothing) x)
      undefined
    Just (d, _) -> return d




foo :: Syntax.Qual -> [Simple.Type] -> Qual
foo []     tys = error "foo"
foo [s]    tys = [(s, tys)]
foo (s:ss) tys = (s, []) : foo ss tys

elaborateRules :: Simple.Type -> Simple.Term -> [(Syntax.Pat, M Simple.Term)] -> M Simple.Term
elaborateRules ty t1 rs =
  case ty of
    Simple.ArrowType ty1 ty2 -> undefined
    Simple.StringType -> undefined
    Simple.TupleType tys ->
      case rs of
        [(Syntax.LowerPat _ x, m)] -> do
          d <- gen
          t2 <- withLowerBind d x m
          return $ Simple.BindTerm d t1 t2
        rs ->
          undefined
    Simple.UnitType ->
      case rs of
        [(Syntax.LowerPat _ x, m)] -> do
          d <- gen
          t2 <- withLowerBind d x m
          return $ Simple.BindTerm d t1 t2
        [(Syntax.UnitPat _, m)] -> do
          d <- gen
          t2 <- m
          return $ Simple.BindTerm d t1 t2
        _ -> error "elaborateRules"
    Simple.SumType d -> undefined

{-
elaborateRules ty t1 rs =
bar :: [(Simple.Term, [Syntax.Pat])] -> [M Simple.Term] -> M Simple.Term
bar [(tys, t1, ps)] t2s = undefined tys t1 ps t2s
bar ((tys, t1, ps) : rs) t2s = undefined tys t1 ps ()

elaborateTupleRules :: (Syntax.Pat, M Simple.Term) -> (Syntax.Pat, M Simple.Term)
elaborateTupleRules (Syntax.TuplePat (p:ps), m) = (p, foldl elaborateTupleRules2 m ps)
elaborateTupleRules _ = error "elaborateTupleRules"

elaborateTupleRules2 :: M Simple.Term -> Syntax.Pat -> M Simple.Term
elaborateTupleRules2 m p = 
-}

elaborateType :: Type.Type -> M Simple.Type
elaborateType ty =
  case ty of
    Type.Arrow ty1 ty2 -> do
      ty1 <- elaborateType ty1
      ty2 <- elaborateType ty2
      return $ Simple.ArrowType ty1 ty2
    Type.Metavariable _ ->
      error "elaborateType"
    Type.String ->
      return $ Simple.StringType
    Type.Tuple tys -> do
      tys <- mapM elaborateType tys
      return $ Simple.TupleType tys
    Type.Unit ->
      return $ Simple.UnitType
    Type.Variable x ->
      getTypeVariable x
    Type.Variant q tys -> do
      tys <- mapM elaborateType tys
      getVariantType q tys

type M a = [a]

-- This should be a simple lookup from a dictionary.
getTypeVariable :: String -> M Simple.Type
getTypeVariable = undefined

-- This registers a variant type as being needed.
getVariantType :: [String] -> [Simple.Type] -> M Simple.Type
getVariantType = undefined

elaborateLambda :: [Syntax.Pat] -> Syntax.Term -> M Simple.Term
elaborateLambda = undefined

-- Get the identifier for a lower-case variable.
getLower :: String -> M Simple.Ident
getLower = undefined

getWork :: M [M ()]
getWork = undefined

setWork :: [M ()] -> M ()
setWork = undefined




-- lookupFun could return the environment where it is found rather than the
-- path. we can then use this to lookup fields. this way the full path is only
-- used for gensym and nothing else.


fullyLookupSum :: String -> [String] -> [[Syntax.Dec]] -> [String]
fullyLookupSum s1 ns dss = resolve [] [last dss] (lookupSum s1 ns dss) (last dss)

fullyLookupFun :: String -> [String] -> [[Syntax.Dec]] -> [String]
fullyLookupFun s1 ns dss = resolve [] [last dss] (lookupFun s1 ns dss) (last dss)

fullyLookupMod :: String -> [String] -> [[Syntax.Dec]] -> [String]
fullyLookupMod s1 ns dss = resolve [] [last dss] (lookupMod s1 ns dss) (last dss)

-- Returns the path for the internal name.
lookupSum :: String -> [String] -> [[Syntax.Dec]] -> [String]
lookupSum s1 ns       ((Syntax.SumDec _ s2 _ _ : ds) : dss) | s1 == s2  = reverse ns
                                                            | otherwise = lookupSum s1 ns (ds : dss)
lookupSum s1 ns       ((_ : ds) : dss)                                  = lookupSum s1 ns (ds : dss)
lookupSum s1 (_ : ns) ([]       : dss)                                  = lookupSum s1 ns dss
lookupSum _ _ _ = undefined

-- Returns the path for the internal name.
lookupFun :: String -> [String] -> [[Syntax.Dec]] -> [String]
lookupFun s1 ns       ((Syntax.FunDec _ s2 _ _ _ _ : ds) : dss) | s1 == s2  = reverse ns
                                                                | otherwise = lookupFun s1 ns (ds : dss)
lookupFun s1 ns       ((_ : ds) : dss)                                      = lookupFun s1 ns (ds : dss)
lookupFun s1 (_ : ns) ([]       : dss)                                      = lookupFun s1 ns dss
lookupFun _ _ _ = undefined

lookupMod :: String -> [String] -> [[Syntax.Dec]] -> [String]
lookupMod s1 ns       ((Syntax.ModDec _ s2 _         : ds) : dss) | s1 == s2  = reverse ns
                                                                  | otherwise = lookupMod s1 ns (ds : dss)
lookupMod s1 ns       ((Syntax.SubDec _ s2 (s' : q') : ds) : dss) | s1 == s2  = lookupMod s' (tail ns) (tail dss) ++ q'
                                                                  | otherwise = lookupMod s1 ns (ds : dss)
lookupMod s1 ns       ((_ : ds) : dss)                                        = lookupMod s1 ns (ds : dss)
lookupMod s1 (_ : ns) ([]       : dss)                                        = lookupMod s1 ns dss
lookupMod _ _ _ = undefined

-- Resolve any aliases in the path.
resolve :: [String] -> [[Syntax.Dec]] -> [String] -> [Syntax.Dec] -> [String]
resolve ns dss [] _ = []
resolve ns dss (s1 : q) (Syntax.ModDec _ s2 ds'     : ds) | s1 == s2  = s1 : resolve (s2 : ns) (ds' : dss) q ds'
                                                          | otherwise = resolve ns dss (s1 : q) ds
resolve ns dss (s1 : q) (Syntax.SubDec _ s2 (s':q') : ds) | s1 == s2  = resolve [] [last dss] (lookupMod s' (tail ns) (tail dss) ++ q) (last dss)
                                                          | otherwise = resolve ns dss (s1 : q) ds
resolve ns dss (s1 : q) (_                          : ds)             = resolve ns dss (s1 : q) ds
resolve _ _ _ _ = undefined






-- Given an environment and a function path, we return the
-- identifier of the function.
funIdentWithPath :: Path -> M Simple.Ident
funIdentWithPath r q = do
  r <- getEnv
  let q' = envFunPathWithPath r q
  x <- lookupFun q'
  case x of 
    Nothing -> do
      d <- gen
      return d
    Just d ->
      return d



-- Given an enviroment and a function path, we return the
-- full path to the function as well as the monad to generate
-- the function.
envInternalGetFunWithPath :: Env -> Path -> (Path, M ())
envInternalGetFunWithPath = undefined



boo :: Env -> Syntax.Dec -> String -> Maybe (String, ())
boo r (Syntax.ModDec _ s1 ds) s2 | s1 == s2 = Just (s1, ())
boo r (Syntax.SubDec _ s1  q) s2 | s1 == s2 = undefined
boo _ _ _ = Nothing

type Env = [(String, ())]
type Path = [(String, [Simple.Type])]

-- Returns the environment which contains the function with the name.
envInternalGetFun :: Env -> String -> Env
envInternalGetFun = undefined

-- Returns the environment of the module.
envInternalGet :: Env -> String -> Env
envInternalGet = undefined

-- Returns the environment with the module field name.
envExternalGetMod :: Env -> String -> Env
envExternalGetMod = undefined

-- Resolves the list of module fields.
envResolve :: Env -> [String] -> Env
envResolve r q = foldl envExternalGetMod r q


envInternalGetFunPath :: Env -> [String] -> [String]
envInternalGetFunPath r []    = unreachable "envInternalGetFunPath"
envInternalGetFunPath r [s]   = envPath (envInternalGetFun r s) ++ [s]
envInternalGetFunPath r (s:q) = envPath (envResolve (envInternalGet r s) q) ++ [s]

-- Returns the full path to the contents of the environment.
envPath :: Env -> [String]
envPath = tail . map fst

envPop :: Env -> Env
envPop = tail
-}

{-
unreachable :: String -> a
unreachable = error . ("unreachable: " ++)

dropLast :: [a] -> [a]
dropLast [] = unreachable "dropLast"
dropLast [x] = []
dropLast (x:xs) = x : dropLast xs

search :: (a -> Maybe b) -> [a] -> Maybe b
search f [] = Nothing
search f (x:xs) = maybe (search f xs) Just (f x)
-}