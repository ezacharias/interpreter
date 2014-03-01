module Compiler.Elaborator where

import qualified Data.IntMap     as IdentMap
import           Data.Map        (Map)
import qualified Data.Map        as Map
import           Data.Maybe      (fromMaybe)

import qualified Compiler.Simple as Simple
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

type IdentMap = IdentMap.IntMap

elaborate :: Syntax.Program -> Simple.Program
elaborate p = run p $ do
  d <- getFun (Type.Path [(Type.Name "Main" [])])
  finish
  x1 <- getProgramTags
  x2 <- getProgramSums
  x3 <- getProgramFuns
  return $ Simple.Program x1 x2 x3 d

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

-- Returns the full path of the function as well as a function to elaborate it.
envGetFun :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetFun r (Type.Path [n])    = envGetFunWithName r n
envGetFun r (Type.Path (n:ns)) = envGetFunWithFields (envGetModWithName r n) (Type.Path ns)
envGetFun r (Type.Path [])     = unreachable "envGetFun"

envGetFunWithName :: Env -> Type.Name -> (Type.Path, Simple.Ident -> M ())
envGetFunWithName (Env []) (Type.Name "Exit" []) = (Type.Path [Type.Name "Exit" []], primitiveExit)
envGetFunWithName (Env []) (Type.Name "Unreachable" [ty]) = (Type.Path [Type.Name "Unreachable" [ty]], primitiveUnreachable ty)
envGetFunWithName (Env []) n = unreachable $ "envGetFunWithName: " ++ show n
envGetFunWithName (Env r@((_, q, _, ds) : r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetFunWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps _ t | s1 == s2 ->
              let q' = Type.pathAddName q (Type.Name s1 tys)
                  r0 = (Nothing, Type.Path [], zip ss tys, []) : r
                  f d = withEnv (Env r0) $ do
                    ty0s <- mapM updateType ty0s
                    ty0 <- updateType ty0
                    t <- elaborateLambda ps ty0s t
                    ty0s <- mapM elaborateType ty0s
                    ty0 <- elaborateType ty0
                    ty <- return $ foldr Simple.ArrowType ty0 ty0s
                    addFun d (Simple.Fun ty t)
               in Just (q', f)
            _ ->
              Nothing

envGetFunWithFields :: Env -> Type.Path -> (Type.Path, Simple.Ident -> M ())
envGetFunWithFields (Env []) _ = unreachable "envGetFunWithFields"
envGetFunWithFields _ (Type.Path []) = unreachable "envGetFunWithFields"
envGetFunWithFields (Env r@((_, Type.Path q, _, ds):r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.FunDec _ ty0s ty0 s2 ss ps _ t | s1 == s2 ->
              let q' = q ++ [Type.Name s1 tys]
                  r0 = (Nothing, Type.Path [], zip ss tys, []) : r
                  f d = withEnv (Env r0) $ do
                    ty0s <- mapM updateType ty0s
                    ty0 <- updateType ty0
                    t <- elaborateLambda ps ty0s t
                    ty0s <- mapM elaborateType ty0s
                    ty0 <- elaborateType ty0
                    ty <- return $ foldr Simple.ArrowType ty0 ty0s
                    addFun d (Simple.Fun ty t)
               in Just (Type.Path q', f)
            _ ->
              Nothing
envGetFunWithFields (Env r@((_, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetFunWithFields"
        check (Just r'') = envGetFunWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              Just (envGetUnit (Env r) (convertQual s3s (map (envUpdateType (Env r)) ty2s)) (Type.pathAddName q (Type.Name s1 tys)))
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

envGetSumWithName :: Env -> Type.Name -> (Type.Path, Simple.Ident -> M ())
envGetSumWithName (Env []) (Type.Name "Output" []) = (Type.Path [Type.Name "Output" []], primitiveOutput)
envGetSumWithName (Env []) n = unreachable $ "envGetSumWithName: " ++ show n
envGetSumWithName (Env r@((_, q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
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

primitiveOutput :: Simple.Ident -> M ()
primitiveOutput d =
  addSum d $ Simple.Sum [[]]

envGetMod :: Env -> Type.Path -> Env
envGetMod r (Type.Path q) =
  case q of
    [] -> unreachable "envGetMod"
    n:ns -> envGetModWithFields (envGetModWithName r n) (Type.Path ns)

envGetModWithName :: Env -> Type.Name -> Env
envGetModWithName (Env []) _ = unreachable "envGetModWithName"
envGetModWithName (Env r@((_, q, _, ds):r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetModWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.pathAddName q (Type.Name s1 []) , [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              todo "envGetModWithName"
            Syntax.SubDec _ s2 q2 | s1 == s2 ->
              -- Note that r' is used because alias lookup starts at the outer level.
              Just (envGetMod (Env r') (convertQual q2 []))
            _ ->
              Nothing

envGetModWithFields :: Env -> Type.Path -> Env
envGetModWithFields (Env []) _ = unreachable "envGetModWithFields"
envGetModWithFields r (Type.Path []) = r
envGetModWithFields (Env r@((_, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetMod"
        check (Just r'') = envGetModWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              Just (envGetUnit (Env r) (convertQual s3s ty2s) (Type.pathAddName q (Type.Name s1 tys)))
            _ ->
              Nothing

-- The second path is the full name of the new instance.
envGetUnit :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnit _ (Type.Path [])     = unreachable "envGetUnit"
envGetUnit r (Type.Path [n])    = envGetUnitWithName r n
envGetUnit r (Type.Path (n:ns)) = envGetUnitWithFields (envGetModWithName r n) (Type.Path ns)

envGetUnitWithName :: Env -> Type.Name -> (Type.Path -> Env)
envGetUnitWithName (Env []) _ = unreachable "envGetUnitWithName"
envGetUnitWithName (Env r@((_, q, _, ds) : r')) (Type.Name s1 tys) = check $ search has ds
  where check Nothing = envGetUnitWithName (Env r') (Type.Name s1 tys)
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              Just (\ q' -> Env ((Just (Type.pathAddName q (Type.Name s1 tys)), q', zip s3s tys, ds) : r))
            _ ->
              Nothing

envGetUnitWithFields :: Env -> Type.Path -> (Type.Path -> Env)
envGetUnitWithFields (Env []) _ = unreachable "envGetUnitWithFields"
envGetUnitWithFields _ (Type.Path []) = unreachable "envGetUnitWithFields"
envGetUnitWithFields (Env r@((_, q, _, ds) : r')) (Type.Path [Type.Name s1 tys]) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just x) = x
        has dec =
          case dec of
            Syntax.UnitDec _ s2 s3s ds | s1 == s2 ->
              Just (\ q' -> Env ((Just (Type.pathAddName q (Type.Name s1 tys)), q', zip s3s tys, ds) : r))
            _ ->
              Nothing
envGetUnitWithFields (Env r@((_, q, _, ds):r')) (Type.Path ((Type.Name s1 tys):ns)) = check $ search has ds
  where check Nothing = unreachable "envGetUnitWithFields"
        check (Just r'') = envGetUnitWithFields r'' (Type.Path ns)
        has dec =
          case dec of
            Syntax.ModDec _ s2 ds | s1 == s2 ->
              Just (Env ((Nothing, Type.pathAddName q (Type.Name s1 tys), [], ds) : r))
            Syntax.NewDec _ ty2s s2 s3s _ | s1 == s2 ->
              Just (envGetUnit (Env r) (convertQual s3s ty2s) (Type.pathAddName q (Type.Name s1 tys)))
            -- Should units support aliases?
            _ ->
              Nothing

primitiveExit :: Int -> M ()
primitiveExit d =
  addFun d $ Simple.Fun (Simple.SumType 0) (Simple.ConstructorTerm 0 0 [])

primitiveUnreachable :: Type.Type -> Int -> M ()
primitiveUnreachable ty d = do
  ty <- elaborateType ty
  addFun d $ Simple.Fun ty (Simple.UnreachableTerm ty)

-- The types have already been updated.
elaborateLambda :: [Syntax.Pat] -> [Type.Type] -> Syntax.Term -> M Simple.Term
elaborateLambda []     []       t = elaborateTerm t
elaborateLambda (p:ps) (ty:tys) t = do
  d <- gen
  withPat d p $ do
    t <- elaborateLambda ps tys t
    ty <- elaborateType ty
    return $ Simple.LambdaTerm d ty t
elaborateLambda _ _ _ = unreachable "elaborateLambda"

-- The type should have already been updated, meaning variant paths have been
-- updated and there are no variables.
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
    Type.Variable x ->
      unreachable "elaborateType"
    Type.Variant q -> do
      d <- getSum q
      return $ Simple.SumType d

-- Resolves any type variables in the path and handles units.
updatePath :: Type.Path -> M Type.Path
updatePath q = do
  r <- getEnv
  return $ envUpdatePath r q

envUpdatePath :: Env -> Type.Path -> Type.Path
envUpdatePath r q =
  envUnitPath r (Type.Path (map (envUpdateName r) (Type.pathNames q)))

updateName :: Type.Name -> M Type.Name
updateName (Type.Name s tys) = do
  tys <- mapM updateType tys
  return $ Type.Name s tys

envUpdateName :: Env -> Type.Name -> Type.Name
envUpdateName r (Type.Name s tys) = Type.Name s (map (envUpdateType r) tys)

-- Removes type variables.
updateType :: Type.Type -> M Type.Type
updateType ty = do
  r <- getEnv
  return $ envUpdateType r ty

envUpdateType :: Env -> Type.Type -> Type.Type
envUpdateType r ty =
  case ty of
    Type.Arrow ty1 ty2 ->
      Type.Arrow (envUpdateType r ty1) (envUpdateType r ty2)
    Type.Metavariable _ ->
      unreachable "envUpdateType"
    Type.String ->
      Type.String
    Type.Tuple tys ->
      Type.Tuple (map (envUpdateType r) tys)
    Type.Unit ->
       Type.Unit
    Type.Variable x ->
       envGetLowerType r x
    Type.Variant q -> do
      Type.Variant (envUpdatePath r q)

envUnitPath :: Env -> Type.Path -> Type.Path
envUnitPath (Env r) q1 = check $ search f r
  where check Nothing  = q1
        check (Just x) = x
        f (Nothing, q3, _, _) = Nothing
        f (Just q2, q3, _, _) = tryUnitPath q1 q2 q3

-- If the start of the first path matches the second, add the third to the rest of the first path.
tryUnitPath :: Type.Path -> Type.Path -> Type.Path -> Maybe Type.Path
tryUnitPath (Type.Path q1) (Type.Path []) (Type.Path q3) = Just (Type.Path (q3 ++ q1))
tryUnitPath (Type.Path (n1:n1s)) (Type.Path (n2:n2s)) q3 | n1 == n2 = tryUnitPath (Type.Path n1s) (Type.Path n2s) q3
tryUnitPath _ _ _ = Nothing

-- Lookup up the type in the environment.
getLowerType :: String -> M Type.Type
getLowerType s = do
  r <- getEnv
  return $ envGetLowerType r s

envGetLowerType :: Env -> String -> Type.Type
envGetLowerType (Env []) s = unreachable "envGetLowerType"
envGetLowerType (Env ((_, _, xs, _) : r)) s = fromMaybe (envGetLowerType (Env r) s) (lookup s xs)

-- This only works for singleton constructors.
withPat :: Simple.Ident -> Syntax.Pat -> M Simple.Term -> M Simple.Term
withPat d pat m =
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
    -- Singleton cases are converted to tuples.
    Syntax.UpperPat _ _ _ _ ps ->
      case ps of
        [] -> m
        [p] -> withPat d p m
        (_:_:_) -> do
          ds <- mapM (const gen) ps
          t <- withPats ds ps m
          return $ Simple.UntupleTerm ds (Simple.VariableTerm d) t

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
    Syntax.BindTerm _ p t1 t2 -> do
      d <- gen
      t1 <- elaborateTerm t1
      t2 <- withPat d p (elaborateTerm t2)
      return $ Simple.BindTerm d t1 t2
    Syntax.CaseTerm ty t rs -> do
      t <- elaborateTerm t
      elaborateCase ty t rs
    Syntax.SeqTerm t1 t2 -> do
      d <- gen
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      return $ Simple.BindTerm d t1 t2
    Syntax.UnitTerm _ ->
      return $ Simple.UnitTerm
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

elaborateCase :: Type.Type -> Simple.Term -> [Syntax.Rule] -> M Simple.Term
elaborateCase ty t1 rs =
  case rs of
    -- Empty case statements are replaced with unreachable.
    [] -> do
      ty <- updateType ty
      ty <- elaborateType ty
      return $ Simple.UnreachableTerm ty
    -- Singleton case statements are the same as let bindings.
    [(p, t2)] -> do
      d <- gen
      t2 <- withPat d p (elaborateTerm t2)
      return $ Simple.BindTerm d t1 t2
    (_:_:_) ->
      todo "elaborateCase"

{-
data Format =
   TupleFormat [()]
 | SumFormat Type.Type
 | VariableFormat

format :: [Maybe Syntax.Pat] -> Format
format [] = VariableFormat
format (Nothing : ps) = format ps
format (Just p : ps) =
  case p of
    Syntax.AscribePat _ p _ -> format (Just p : ps)
    Syntax.LowerPat _ _ -> format ps
    Syntax.TuplePat _ _ ps -> TupleFormat (map (const ()) ps)
    Syntax.UnderbarPat -> format ps
    Syntax.UnitPat _ -> format ps
    Syntax.UpperPat _ _ ty _ _ -> SumFormat ty

foo :: [Simple.Ident] -> [([Maybe Syntax.Pat], M Simple.Term)] -> M Simple.Term
foo [] _ = unreachable "foo"
foo ds [(ps, m)] = bar ds ps m
foo (d:ds) rs =
  case format (map (head . fst) rs) of
    TupleFormat xs -> do
      ds2 <- mapM (const gen) xs
      rs <- mapM (barTuple d) rs
      t <- foo (ds2 ++ ds) rs
      return $ Simple.Untuple ds2 (Simple.VariableTerm d) t
    SumFormat Int -> do
      barSum rs
      xs <- undefined
      return $ Simple.Case (Simple.VariableTerm d) xs
    VariableFormat -> do
      rs <- mapM (barVariable d) rs
      foo ds rs

barTuple :: Simple.Ident -> [Maybe Syntax.Pat] -> ([Maybe Syntax.Pat], M Simple.Term) -> M ([Maybe Syntax.Pat], M Simple.Term)
barTuple d ns ([], _) = unreachable "barTuple"
barTuple d ns (Nothing : ps, m) = return (ns ++ ps, m)
barTuple d ns (Just p : ps, m) =
  case p of
    Syntax.AscribePat _ p _ -> barTuple ds d (Just p : ps, m)
    Syntax.LowerPat _ s -> (ns ++ ps, withBind s d m)
    Syntax.TuplePat _ _ ps2 -> (ps2 ++ ps, m)
    Syntax.UnderbarPat -> (ns ++ ps, m)
    Syntax.UnitPat _ -> unreachable "barTuple"
    Syntax.UpperPat _ _ _ _ _ -> unreachable "barTuple"

barVariable :: Simple.Ident -> ([Maybe Syntax.Pat], M Simple.Term) -> M ([Maybe Syntax.Pat], M Simple.Term)
barVariable d ([], _) = unreachable "barTuple"
barVariable d (Nothing : ps, m) = return (ps, m)
barVariable d (Just p : ps, m) =
  case p of
    Syntax.AscribePat _ p _ -> barVariable d (Just p : ps, m)
    Syntax.LowerPat _ s -> (ps, withBind s d m)
    Syntax.TuplePat _ _ ps2 -> unreachable "barVariable"
    Syntax.UnderbarPat -> (ps, m)
    Syntax.UnitPat _ -> (ps, m)
    Syntax.UpperPat _ _ _ _ _ -> unreachable "barTuple"

bar :: [(Syntax.Pat, Simple.Ident)] -> M Simple.Term -> M Simple.Term
bar [] m = m
bar ((p, d) : rs) m = elaborateBind p (Simple.VariableTerm d) (bar rs m)

bat :: Syntax.Pat -> Simple.Ident -> [([(Syntax.Pat, Simple.Ident)], M Simple.Term)] -> M Simple.Term
bat p d rs =
  case p of
    Syntax.AscribePat _ p _ ->
      bat p d rs
    Syntax.LowerPat _ _ ->
      unreachable "bat"
    Syntax.TuplePat _ _ ps -> do
      ds <- mapM (const gen) ps
      let rs' = map (expandTuple ds) rs
      t <- foo rs
      return $ Simple.UntupleTerm ds (Simple.VariableTerm d) t
    Syntax.UnderbarPat ->
      unreachable "bat"
    Syntax.UnitPat _ ->
      unreachable "bat"
    Syntax.UpperPat _ _ _ _ _ -> do
      todo "bat"

expandTuple :: [Simple.Ident] -> ([(Syntax.Pat, Simple.Ident)], M Simple.Term) -> ([(Syntax.Pat, Simple.Ident)], M Simple.Term)
expandTuple ds ((Syntax.AscribePat _ p _, d) : xs, m) = expandTuple ds ((p, d) : xs, m)
expandTuple ds ((Syntax.TuplePat _ _ ps, d) : xs, m) = (zip ps ds ++ xs, m)
expandTuple ds _ = unreachable "expandTulpe"
-}

{-
         | UpperPat Pos [Type.Type] Type.Type Qual [Pat]
-}

-- An environment is a possible old path, the full path, the local type bindings, and the declarations.
data Env = Env [(Maybe Type.Path, Type.Path, [(String, Type.Type)], [Syntax.Dec])]

run :: Syntax.Program -> M Simple.Program -> Simple.Program
run (Syntax.Program ds) m = runM m r k genVal [] exportedSums exportedFuns programTags programSums programFuns
  where r = Env [(Nothing, Type.Path [], [], ds)]
        k x _ _ _ _ _ _ _ = x
        genVal = 2
        exportedSums = Map.empty
        exportedFuns = Map.empty
        programTags = IdentMap.empty
        programSums = IdentMap.empty
        programFuns = IdentMap.empty
        {-
        programSums = IdentMap.fromList [ (0, Simple.Sum [[]])
                                        ]
        programFuns = IdentMap.fromList [ (1, Simple.Fun (Simple.SumType 0) (Simple.ConstructorTerm 0 0 []))
                                        ]
        -}

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
