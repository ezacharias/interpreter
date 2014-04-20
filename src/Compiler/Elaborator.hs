module Compiler.Elaborator where

import           Control.Monad   (MonadPlus, forM, liftM, liftM2, mplus, msum,
                                  mzero, (<=<))
import qualified Data.IntMap     as IdentMap
import           Data.Map        (Map)
import qualified Data.Map        as Map
import           Data.Maybe      (fromMaybe)

import qualified Compiler.Simple as Simple
import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type

type IdentMap = IdentMap.IntMap

-- To elaborate we simply get the identifier for Main. This will add
-- elaboration of Main to the work queue. When finish is called, Main will be
-- elaborated, which will in turn add more work to the work queue and so on.
elaborate :: Syntax.Program -> Simple.Program
elaborate p = run $ do
  d <- getFun $ Path [Name "Main" []]
  finish p
  x1 <- get programTags
  x2 <- get programSums
  x3 <- get programFuns
  return $ Simple.Program x1 x2 x3 d

-- Run until the work queue is empty.
finish :: Syntax.Program -> M ()
finish p = do
  w <- get work
  case w of
    [] -> return ()
    (m : w) -> do
      -- It is necessary to set the work queue before running m because m
      -- may modify the work queue.
      set (\ s -> s {work = w})
      m p
      finish p

-- This uses a fully qualified name. First we check to see if the function has
-- already been exported. If not, we export it.
getFun :: Path -> M Simple.Ident
getFun q = do
  x <- get exportedFuns
  case Map.lookup q x of
    Just d -> return d
    Nothing -> do
      d <- gen
      -- It is necessary to set the exported ident before any further work.
      set (\ s -> s {exportedFuns = Map.insert q d x})
      addWork $ exportFun q d
      return d

-- Are we properly handling sums of zero and one constructor with this? This
-- should perhaps return a type.
getSum :: Path -> M Simple.Ident
getSum q = do
  x <- get exportedSums
  case Map.lookup q x of
    Just d -> return d
    Nothing -> do
      case q of
        Path [Name "Output" []] -> do
          set (\ s -> s {exportedSums = Map.insert q 0 x})
          return 0
        -- We need to do more here.
        Path [Name "Stream" [ty1, ty2, ty3]] -> do
          d <- gen
          set (\ s -> s {exportedSums = Map.insert q d x})
          return d
        _ -> do
          d <- gen
          -- It is necessary to set the exported ident before any further work.
          set (\ s -> s {exportedSums = Map.insert q d x})
          addWork $ exportSum q d
          return d

getTag :: Path -> M Simple.Ident
getTag q = do
  x <- get exportedTags
  case Map.lookup q x of
    Just d -> return d
    Nothing -> do
      d <- gen
      -- It is necessary to set the exported ident before any further work.
      set (\ s -> s {exportedTags = Map.insert q d x})
      return d

-- If we use a constructor as a function or in a pattern we must make sure the
-- sum type is exported.
exportFun :: Path -> Simple.Ident -> Syntax.Program -> M ()
exportFun (Path [Name "Continue" []]) d prog = primitiveContinue d
exportFun (Path [Name "Exit" []]) d prog = primitiveExit d
exportFun (Path [Name "Write" []]) d prog = primitiveWrite d
exportFun (Path [Name "End" [ty1, ty2, ty3]]) d prog = primitiveEnd ty1 ty2 ty3 d
exportFun (Path [Name "Next" [ty1, ty2, ty3]]) d prog = primitiveNext ty1 ty2 ty3 d
exportFun (Path [Name "Unreachable" [ty]]) d prog = primitiveUnreachable ty d
exportFun p d prog = do
  let (ns, n) = splitPath p
  let (Syntax.Program decs) = prog
  resolveFields (Path []) prog decs ns $ \ p prog decs ->
    exportFunWithName p d n decs

exportSum :: Path -> Simple.Ident -> Syntax.Program -> M ()
exportSum p d prog = do
  let (ns, n) = splitPath p
  let (Syntax.Program decs) = prog
  resolveFields (Path []) prog decs ns $ \ p prog decs ->
    exportSumWithName d n decs

splitPath :: Path -> ([Name], Name)
splitPath (Path ns) =
  case reverse ns of
    [] -> unreachable "splitPath"
    (n:ns) -> (reverse ns, n)

resolveFields :: Path -> Syntax.Program -> [Syntax.Dec] -> [Name] -> (Path -> Syntax.Program -> [Syntax.Dec] -> M a)-> M a
resolveFields p prog decs ns m =
  case ns of
    [] -> m p prog decs
    (n:ns) -> resolveField n (pathAddName p n) prog decs $ \ p prog decs ->
                resolveFields p prog decs ns m

pathAddName :: Path -> Name -> Path
pathAddName (Path ns) n = Path (reverse (n : reverse ns))

resolveField :: Name -> Path -> Syntax.Program -> [Syntax.Dec] -> (Path -> Syntax.Program -> [Syntax.Dec] -> M a)-> M a
resolveField n p prog decs m = fromMaybe (unreachable $ "resolveField: " ++ show n) (search (hasField p prog n m) decs)

hasField :: Path -> Syntax.Program -> Name -> (Path -> Syntax.Program -> [Syntax.Dec] -> M a) -> Syntax.Dec -> Maybe (M a)
hasField p prog (Name s1 ty1s) m dec =
  case dec of
    Syntax.ModDec _ s2 vs decs | s1 == s2 -> Just $ do
      withTypeVariables (zip vs ty1s) $ do
        m p prog decs
    Syntax.NewDec _ (Type.Path ns) s2 vs _ | s1 == s2 -> Just $ do
      case ns of
        [Type.Name "Escape" [ty1, ty2]] -> do
          ty1 <- groundType ty1
          ty2 <- groundType ty2
          withTypeVariables [("a", ty1), ("b", ty2)] $ do
            m p prog []
        _ -> do
          let Syntax.Program decs = prog
          withTypeVariables (zip vs ty1s) $ do
            ns <- mapM groundName ns
            p2 <- return $ Path ns
            withRename (createRename p2 p) $ do
              resolveFields (Path []) prog decs ns m
    Syntax.UnitDec _ s2 vs decs | s1 == s2 -> Just $ do
      withTypeVariables (zip vs ty1s) $ do
        m p prog decs
    _ -> Nothing

exportFunWithName :: Path -> Simple.Ident -> Name -> [Syntax.Dec] -> M ()
exportFunWithName p d n decs =
  case n of
    Name "Catch" [ty] -> do
      d2 <- getTag p
      primitiveCatch d2 d ty
    Name "Throw" [] -> do
      d2 <- getTag p
      primitiveThrow d2 d
    _ ->
      fromMaybe (unreachable $ "exportFunWithName: " ++ show n) (search (hasFunWithName d n) decs)

exportSumWithName :: Simple.Ident -> Name -> [Syntax.Dec] -> M ()
exportSumWithName d n decs =
  fromMaybe (unreachable "exportSumWithName") (search (hasSumWithName d n) decs)

hasFunWithName :: Simple.Ident -> Name -> Syntax.Dec -> Maybe (M ())
hasFunWithName d (Name s1 ty1s) dec =
  case dec of
    Syntax.FunDec _ ty2s ty2 s2 vs pats _ t | s1 == s2 -> Just $ do
      withTypeVariables (zip vs ty1s) $ do
        ty2s <- mapM groundType ty2s
        ty2 <- groundType ty2
        ty2s <- mapM elaborateType ty2s
        ty2 <- elaborateType ty2
        t <- elaborateLambda pats ty2s t
        addFun d (Simple.Fun (foldr Simple.ArrowType ty2 ty2s) t)
    Syntax.SumDec _ q s2 vs cs ->
      let has (i, (_, ty2s, s3, _)) | s1 == s3 = Just $ do
            withTypeVariables (zip vs ty1s) $ do
              ty2s <- mapM groundType ty2s
              ty2s <- mapM elaborateType ty2s
              d2s <- mapM (const gen) ty2s
              q <- groundPath q
              d3 <- getSum q
              let t2 = Simple.ConstructorTerm d3 i (map Simple.VariableTerm d2s)
              addFun d (Simple.Fun (foldr Simple.ArrowType (Simple.SumType d3) ty2s)
                         (foldr (\ (d2, ty2) t2 -> Simple.LambdaTerm d2 ty2 t2) t2 (zip d2s ty2s)))
          has _ = Nothing
       in search has (zip [0..] cs)
    _ -> Nothing

hasSumWithName :: Simple.Ident -> Name -> Syntax.Dec -> Maybe (M ())
hasSumWithName d (Name s1 ty1s) dec =
  case dec of
    Syntax.SumDec _ q s2 vs cs | s1 == s2 -> Just $ do
      withTypeVariables (zip vs ty1s) $ do
        tyss <- mapM (\ (_, tys, _, _) -> mapM (elaborateType <=< groundType) tys) cs
        addSum d (Simple.Sum tyss)
    _ -> Nothing

primitiveContinue :: Int -> M ()
primitiveContinue d1 = do
  d2 <- gen
  addFun d1 $ Simple.Fun (Simple.ArrowType (Simple.ArrowType Simple.UnitType
                                                             (Simple.SumType 0))
                                           (Simple.SumType 0))
                (Simple.LambdaTerm d2 (Simple.ArrowType Simple.UnitType
                                                        (Simple.SumType 0))
                  (Simple.ConstructorTerm 0 2 [Simple.VariableTerm d2]))

primitiveExit :: Int -> M ()
primitiveExit d =
  addFun d $ Simple.Fun (Simple.SumType 0) (Simple.ConstructorTerm 0 0 [])

primitiveWrite :: Int -> M ()
primitiveWrite d1 = do
  d2 <- gen
  d3 <- gen
  addFun d1 $ Simple.Fun (Simple.ArrowType Simple.StringType
                                           (Simple.ArrowType (Simple.SumType 0)
                                                             (Simple.SumType 0)))
                (Simple.LambdaTerm d2 Simple.StringType
                  (Simple.LambdaTerm d3 (Simple.SumType 0)
                    (Simple.ConstructorTerm 0 1 [Simple.VariableTerm d2, Simple.VariableTerm d3])))

primitiveEnd :: Type -> Type -> Type -> Int -> M ()
primitiveEnd ty1 ty2 ty3 d1 = do
  d2 <- getSum (Path [Name "Stream" [ty1, ty2, ty3]])
  d3 <- gen
  ty3 <- elaborateType ty3
  addFun d1 $ Simple.Fun (Simple.ArrowType ty3 (Simple.SumType d2))
                (Simple.LambdaTerm d3 ty3
                  (Simple.ConstructorTerm d2 0 [Simple.VariableTerm d3]))

primitiveNext :: Type -> Type -> Type -> Int -> M ()
primitiveNext ty1 ty2 ty3 d1 = do
  d2 <- getSum (Path [Name "Stream" [ty1, ty2, ty3]])
  d3 <- gen
  d4 <- gen
  ty1 <- elaborateType ty1
  ty2 <- elaborateType ty2
  addFun d1 $ Simple.Fun (Simple.ArrowType ty1
                                           (Simple.ArrowType (Simple.ArrowType ty2 (Simple.SumType d2))
                                                             (Simple.SumType d2)))
                (Simple.LambdaTerm d3 ty1
                  (Simple.LambdaTerm d4 (Simple.ArrowType ty2 (Simple.SumType d2))
                    (Simple.ConstructorTerm d2 1 [Simple.VariableTerm d3, Simple.VariableTerm d4])))

primitiveUnreachable :: Type -> Int -> M ()
primitiveUnreachable ty d = do
  ty <- elaborateType ty
  addFun d $ Simple.Fun ty (Simple.UnreachableTerm ty)

primitiveThrow :: Int -> Int -> M ()
primitiveThrow tag d = do
  d2 <- gen
  ty1 <- getTypeVariable "a"
  ty1 <- elaborateType ty1
  ty2 <- getTypeVariable "b"
  ty2 <- elaborateType ty2
  addFun d $ Simple.Fun (Simple.ArrowType ty1 ty2)
               (Simple.LambdaTerm d2 ty1
                 (Simple.ThrowTerm tag (Simple.VariableTerm d2)))

primitiveCatch :: Int -> Int -> Type -> M ()
primitiveCatch tag d ty3 = do
  ty1 <- getTypeVariable "a"
  ty2 <- getTypeVariable "b"
  d2 <- getSum (Path [Name "Stream" [ty1, ty2, ty3]])
  d3 <- gen
  ty3 <- elaborateType ty3
  addFun d $ Simple.Fun (Simple.ArrowType (Simple.ArrowType Simple.UnitType ty3)
                                          (Simple.SumType d2))
               (Simple.LambdaTerm d3 (Simple.ArrowType Simple.UnitType ty3)
                 (Simple.CatchTerm tag d2
                   (Simple.ApplyTerm (Simple.VariableTerm d3) Simple.UnitTerm)))

elaborateType :: Type -> M Simple.Type
elaborateType ty = do
  case ty of
    Arrow ty1 ty2 -> do
      ty1 <- elaborateType ty1
      ty2 <- elaborateType ty2
      return $ Simple.ArrowType ty1 ty2
    String ->
      return $ Simple.StringType
    Tuple tys -> do
      tys <- mapM elaborateType tys
      return $ Simple.TupleType tys
    Unit ->
       return $ Simple.UnitType
    Sum q -> do
      d <- getSum q
      return $ Simple.SumType d

elaborateLambda :: [Syntax.Pat] -> [Simple.Type] -> Syntax.Term -> M Simple.Term
elaborateLambda []     []       t = elaborateTerm t
elaborateLambda (p:ps) (ty:tys) t = do
  d <- gen
  withPat d p $ do
    t <- elaborateLambda ps tys t
    return $ Simple.LambdaTerm d ty t
elaborateLambda _ _ _ = unreachable "elaborateLambda"

-- This only works for singleton constructors.
withPat :: Simple.Ident -> Syntax.Pat -> M Simple.Term -> M Simple.Term
withPat d pat m =
  case pat of
    Syntax.AscribePat _ _ p _ ->
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
    Syntax.UpperPat _ _ _ _ _ _ ps -> do
      ds <- mapM (const gen) ps
      t <- withPats ds ps m
      return $ Simple.CaseTerm (Simple.VariableTerm d) [(ds, t)]

withPats :: [Simple.Ident] -> [Syntax.Pat] -> M Simple.Term -> M Simple.Term
withPats [] [] m = m
withPats (d:ds) (p:ps) m = withPat d p (withPats ds ps m)
withPats _ _ _ = unreachable "withPats"

-- This does not, from what I can see, require a type.
withLowerBind :: String -> Simple.Ident -> M Simple.Term -> M Simple.Term
withLowerBind s d m =
  with (\ o -> o {valueVariables = (s, d) : valueVariables o}) m

getLowerBind :: String -> M Simple.Ident
getLowerBind s = do
  r <- look valueVariables
  return $ fromMaybe (unreachable "getLowerBind") (lookup s r)

inUnit :: Type.Path -> ([Syntax.Dec] -> Maybe (M ())) -> M a
inUnit = todo "inUnit"

elaborateTerm :: Syntax.Term -> M Simple.Term
elaborateTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      return $ Simple.ApplyTerm t1 t2
    Syntax.AscribeTerm _ _ t _ ->
      elaborateTerm t
    Syntax.BindTerm _ p t1 t2 -> do
      d <- gen
      t1 <- elaborateTerm t1
      t2 <- withPat d p (elaborateTerm t2)
      return $ Simple.BindTerm d t1 t2
    Syntax.CaseTerm _ t1 rs -> do
      p <- return $ createPatFromRules rs
      d <- gen
      t1 <- elaborateTerm t1
      t2 <- generateFromPat d p (\ v -> findRule (d, v) rs)
      return $ Simple.BindTerm d t1 t2
    Syntax.ForTerm ty1s ty2 ps t1 t2 -> do
      t1 <- elaborateTerm t1
      ty1s <- mapM groundType ty1s
      ty1s <- mapM elaborateType ty1s
      t2 <- elaborateLambda ps ty1s t2
      return $ Simple.ApplyTerm t1 t2
    Syntax.StringTerm _ x ->
      return $ Simple.StringTerm x
    Syntax.SeqTerm t1 t2 -> do
      d <- gen
      t1 <- elaborateTerm t1
      t2 <- elaborateTerm t2
      return $ Simple.BindTerm d t1 t2
    Syntax.TupleTerm _ _ ts -> do
      ts <- mapM elaborateTerm ts
      return $ Simple.TupleTerm ts
    Syntax.UnitTerm pos ->
      return $ Simple.UnitTerm
    Syntax.UpperTerm _ q _ _ -> do
      q <- groundPath q
      d <- getFun q
      return $ Simple.FunTerm d
    Syntax.VariableTerm _ s -> do
      d <- getLowerBind s
      return $ Simple.VariableTerm d



data Pat =
   EmptyPat
 | TuplePat [Pat]
 | CasePat [(String, [Pat])]

createPatFromRules :: [Syntax.Rule] -> Pat
createPatFromRules rs = foldl createPat EmptyPat (map fst rs)

createPat :: Pat -> Syntax.Pat -> Pat
createPat p1 p2 =
  case (p1, p2) of
    (p1, Syntax.AscribePat _ _ p2 _) -> createPat p1 p2
    (p1, Syntax.LowerPat _ _) -> p1
    (EmptyPat, Syntax.TuplePat _ _ p2s) -> TuplePat (map (createPat EmptyPat) p2s)
    (TuplePat p1s, Syntax.TuplePat _ _ p2s) -> TuplePat (zipWith createPat p1s p2s)
    (CasePat _, Syntax.TuplePat _ _ p3s) -> unreachable "createPathFromRule"
    (p1, Syntax.UnderbarPat) -> p1
    (p1, Syntax.UnitPat _) -> p1
    (EmptyPat, Syntax.UpperPat _ _ _ _ xs q p2s) -> CasePat (map (\ (q, ys) -> (q, map (const EmptyPat) ys)) xs)
    (TuplePat p1s, Syntax.UpperPat _ _ _ _ _ q p2s) -> unreachable "createPat"
    (CasePat xs, Syntax.UpperPat _ q2 _ _ _ _ p2s) -> let s2 = pathNameString q2
                                                       in CasePat (map (\ (s1, p1s) -> if s1 == s2 then (s1, zipWith createPat p1s p2s) else (s1, p1s)) xs)

pathNameString :: Type.Path -> String
pathNameString (Type.Path ns) = let Type.Name s _ = last ns in s

generateFromPat :: Simple.Ident -> Pat -> (Val -> M Simple.Term) -> M Simple.Term
generateFromPat d1 p1 k =
  case p1 of
    CasePat xs -> do
      zs <- forM xs $ \ (s, p2s) -> do
        d2s <- mapM (const gen) p2s
        t <- generateFromPats d2s p2s $ \ ys -> do
          k (ConstructorVal s (zip d2s ys))
        return (d2s, t)
      return $ Simple.CaseTerm (Simple.VariableTerm d1) zs
    EmptyPat -> do
      k AnyVal
    TuplePat p2s -> do
      d2s <- mapM (const gen) p2s
      t <- generateFromPats d2s p2s (\ xs -> k (TupleVal (zip d2s xs)))
      return $ Simple.UntupleTerm d2s (Simple.VariableTerm d1) t

generateFromPats :: [Simple.Ident] -> [Pat] -> ([Val] -> M Simple.Term) -> M Simple.Term
generateFromPats [] [] k = k []
generateFromPats (d:ds) (p:ps) k = generateFromPat d p (\ x -> generateFromPats ds ps (\ xs -> k (x:xs)))
generateFromPats _ _ _ = unreachable "generateFromPats"

data Val =
   TupleVal [(Simple.Ident, Val)]
 | ConstructorVal String [(Simple.Ident, Val)]
 | AnyVal

findRule :: (Simple.Ident, Val) -> [(Syntax.Pat, Syntax.Term)] -> M Simple.Term
findRule x rs = fromMaybe (unreachable "findRule") $ msum $ map (tryRule x) rs

-- Returns the elaborated body of the rule if the pattern matches the Val.
tryRule :: MonadPlus m => (Simple.Ident, Val) -> (Syntax.Pat, Syntax.Term) -> m (M Simple.Term)
tryRule x (p, t) = reallyTryRule x p (elaborateTerm t)

reallyTryRule :: MonadPlus m => (Simple.Ident, Val) -> Syntax.Pat -> M Simple.Term -> m (M Simple.Term)
reallyTryRule (d, v) p m =
  case p of
    Syntax.AscribePat _ _ p _ ->
      reallyTryRule (d, v) p m
    Syntax.LowerPat _ s ->
      return $ withLowerBind s d m
    Syntax.TuplePat _ _ ps ->
      case v of
        TupleVal xs -> reallyTryRules xs ps m
        ConstructorVal _ _ -> unreachable "reallyTryRule"
        AnyVal -> unreachable "reallyTryRule"
    Syntax.UnderbarPat ->
      return $ m
    Syntax.UnitPat _ ->
      return $ m
    Syntax.UpperPat _ q1 _ _ _ _ ps ->
      case v of
        TupleVal xs -> unreachable "reallyTryRule"
        ConstructorVal s2 xs ->
          if pathNameString q1 == s2
            then reallyTryRules xs ps m
            else mzero
        AnyVal -> unreachable "reallyTryRule"

reallyTryRules :: MonadPlus m => [(Simple.Ident, Val)] -> [Syntax.Pat] -> M Simple.Term -> m (M Simple.Term)
reallyTryRules [] [] m = return m
reallyTryRules (x:xs) (p:ps) m = reallyTryRule x p =<< reallyTryRules xs ps m
reallyTryRules _ _ _ = unreachable "reallyTryRules"

-- If the start of the third path matches the first path, replace the start
-- with the second path. This is used for unit instantiation.
createRename :: Path -> Path -> (Path -> Path)
createRename (Path n1s) (Path n2s) (Path n3s) = Path $ fromMaybe n3s (createRename2 n1s n2s n3s)

createRename2 :: [Name] -> [Name] -> [Name] -> Maybe [Name]
createRename2 [] n2s n3s = Just $ n2s ++ n3s
createRename2 (n1:n1s) n2s (n3:n3s) | n1 == n3 = createRename2 n1s n2s n3s
createRename2 _ _ _ = Nothing

addWork :: (Syntax.Program -> M ()) -> M ()
addWork m = do
  w <- get work
  set (\ s -> s {work = (m : w)})

addFun :: Simple.Ident -> Simple.Fun -> M ()
addFun d x = do
  xs <- get programFuns
  set (\ s -> s {programFuns = (d, x) : xs})

addSum :: Simple.Ident -> Simple.Sum -> M ()
addSum d x = do
  xs <- get programSums
  set (\ s -> s {programSums = (d, x) : xs})

newtype M a = M { runM :: Look -> (a -> State -> Simple.Program) -> State -> Simple.Program }

data State = State
 { work         :: [Syntax.Program -> M ()]
 , ident        :: Simple.Ident
 , exportedTags :: Map Path Simple.Ident
 , exportedSums :: Map Path Simple.Ident
 , exportedFuns :: Map Path Simple.Ident
 , programTags  :: [(Simple.Ident, Simple.Tag)]
 , programSums  :: [(Simple.Ident, Simple.Sum)]
 , programFuns  :: [(Simple.Ident, Simple.Fun)]
 }

data Look = Look
 { typeVariables  :: [(String, Type)]
 , valueVariables :: [(String, Simple.Ident)]
 , renamer        :: Path -> Path
 }

instance Monad M where
  return x = M (\ o k -> k x)
  m >>= f = M (\ o k -> runM m o (\ x -> runM (f x) o k))

run :: M Simple.Program -> Simple.Program
run m = runM m look (\ x _ -> x) state
  where look = Look { typeVariables = []
                    , valueVariables = []
                    , renamer = id
                    }
        state = State { work = []
                      , ident = 100
                      , exportedTags = Map.empty
                      , exportedSums = Map.empty
                      , exportedFuns = Map.empty
                      , programTags = []
                      , programSums = []
                      , programFuns = []
                      }

renamePath :: Path -> M Path
renamePath q = do f <- look renamer
                  return $ f q

get :: (State -> a) -> M a
get f = M (\ o k d -> k (f d) d)

set :: (State -> State) -> M ()
set f = M (\ o k d -> k () (f d))

look :: (Look -> a) -> M a
look f = M (\ o k d -> k (f o) d)

with :: (Look -> Look) -> M a -> M a
with f m = M (\ o k d -> runM m (f o) k d)

withRename :: (Path -> Path) -> M a -> M a
withRename f m = with (\ o -> o {renamer = renamer o . f}) m

withTypeVariables :: [(String, Type)] -> M a -> M a
withTypeVariables xs m = with (\ o -> o {typeVariables = xs ++ typeVariables o}) m

getTypeVariable :: String -> M Type
getTypeVariable s = do
  r <- look typeVariables
  return $ fromMaybe (unreachable "getTypeVariable") (lookup s r)

gen :: M Simple.Ident
gen = do
  d <- get ident
  set (\ s -> s {ident = d + 1})
  return d

data Path = Path { pathNames :: [Name] }
 deriving (Eq, Ord, Show)

data Name = Name String [Type]
 deriving (Eq, Ord, Show)

data Type = Arrow Type Type
          | String
          | Tuple { tupleElems :: [Type] }
          | Unit
          | Sum Path
 deriving (Eq, Ord, Show)

-- Eliminates type variables and adjusts it for unit instantiation.
groundPath :: Type.Path -> M Path
groundPath (Type.Path ns) = liftM Path (mapM groundName ns) >>= renamePath

groundName :: Type.Name -> M Name
groundName (Type.Name s tys) = liftM (Name s) (mapM groundType tys)

groundType :: Type.Type -> M Type
groundType ty =
  case ty of
    Type.Arrow ty1 ty2 -> liftM2 Arrow (groundType ty1) (groundType ty2)
    Type.Metavariable _ -> unreachable $ "groundType: metavariable"
    Type.String -> return $ String
    Type.Tuple tys -> liftM Tuple (mapM groundType tys)
    Type.Unit -> return $ Unit
    Type.Variable x -> getTypeVariable x
    Type.Variant q -> liftM Sum (groundPath q)


-- Utility Functions

search :: (a -> Maybe b) -> [a] -> Maybe b
search f [] = Nothing
search f (x:xs) = mplus (search f xs) (f x)

todo :: String -> a
todo s = error $ "todo: Elaborator." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Elaborator." ++ s
