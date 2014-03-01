{-
For patterns, we want to analyze the pattern first
and use the incomplete type information as the
expected type of the term. To analyze the pattern,
we must pass an expected type.

We will separate generating pattern bindings from
actual binding so we can reuse the function.

Take something like a pattern in the for notation.
It might complete a concrete type. I need to think
about how to do that.
-}


module Compiler.TypeChecker where

import           Control.Monad   (MonadPlus, mzero)
import           Data.IntMap     (IntMap)
import qualified Data.IntMap     as IntMap
import           Data.List       (intersperse)

import qualified Compiler.Syntax as Syntax
import qualified Compiler.Type   as Type


-- The program syntax starts out containing type metavariables. It either
-- returns a program with all type metavariables replaced by concrete types or
-- it returns an error string.

inferProgram :: Syntax.Program -> Either String Syntax.Program

inferProgram (Syntax.Program xs) =
  fmap Syntax.Program (mapM inferDec xs)


inferDec :: Syntax.Dec -> Either String Syntax.Dec

inferDec (Syntax.SumDec pos s ss rs) =
  Right $ Syntax.SumDec pos s ss rs

-- ty0s and ty0 have been converted in Meta.
inferDec (Syntax.FunDec pos ty0s ty0 s ss ps ty t) = do
  case inferTerm g sigmaEmpty ty0 t of
    Left msg -> Left msg
    Right t -> Right $ Syntax.FunDec pos ty0s ty0 s ss ps ty t
  where g = either (\ _ -> error "impossible") id $ gammaWithPats g sigmaEmpty ps ty0s

inferDec (Syntax.ModDec pos s ds) =
  case inferDecs ds of
    Left msg -> Left msg
    Right ds -> Right $ Syntax.ModDec pos s ds

inferDec (Syntax.NewDec pos tys' s1 s2 tys) =
  Right $ Syntax.NewDec pos tys' s1 s2 tys

inferDec (Syntax.UnitDec pos s tys ds) =
  case inferDecs ds of
    Left msg -> Left msg
    Right ds -> Right $ Syntax.UnitDec pos s tys ds

inferDec (Syntax.SubDec pos x1 x2) =
  Right $ Syntax.SubDec pos x1 x2


inferDecs :: [Syntax.Dec] -> Either String [Syntax.Dec]
inferDecs [] = Right []
inferDecs (d:ds) =
  case inferDec d of
    Left msg -> Left msg
    Right d ->
      case inferDecs ds of
        Left msg -> Left msg
        Right ds -> Right (d:ds)


gammaWithPat :: Gamma -> Sigma -> Syntax.Pat -> Type.Type -> Either String Gamma
gammaWithPat g s (Syntax.AscribePat _ p _)      ty = gammaWithPat g s p ty
gammaWithPat g s (Syntax.LowerPat pos n)        ty = gammaWithLowerPat g s pos n ty
gammaWithPat g s (Syntax.TuplePat _ _ ps)       ty = gammaWithPats g s ps (Type.tupleElems ty)
gammaWithPat g s Syntax.UnderbarPat             ty = Right g
gammaWithPat g s (Syntax.UnitPat _)             ty = Right g
gammaWithPat g s (Syntax.UpperPat _ tys _ _ ps) ty = gammaWithPats g s ps tys


gammaWithPats :: Gamma -> Sigma -> [Syntax.Pat] -> [Type.Type] -> Either String Gamma

gammaWithPats g s []     []       = Right g
gammaWithPats g s (p:ps) (ty:tys) = case gammaWithPat g s p ty of
                                      Left msg -> Left msg
                                      Right g -> gammaWithPats g s ps tys
gammaWithPats g s _      _        = error "Compiler.TypeChecker.withPats: impossible"


gammaWithLowerPat :: Gamma -> Sigma -> Syntax.Pos -> String -> Type.Type -> Either String Gamma
gammaWithLowerPat g s pos n ty =
  if isConcreteType ty'
    then Right $ gammaBind g n ty'
    else Left $ filename ++ ":" ++ show line ++ ":" ++ show col ++ ": Variable bindings must have concrete types. Given " ++ fst (showType [] (updateType s ty')) ++ "."
  where ty' = updateType s ty
        (m, _) = showType [] ty'
        Syntax.Pos filename line col = pos


-- The first thing we do is run typeCheckTerm, which gets us the table of
-- metavariables. We then run updateTerm, which uses the table to replace
-- metavariables with concrete types.

inferTerm :: Gamma -> Sigma -> Type.Type -> Syntax.Term -> Either String Syntax.Term

inferTerm g s ty t = do s <- typeCheckTerm g s ty t
                        return $ concreteTerm s t


-- Replaces all metavariables in the term with concrete types.

concreteTerm :: Sigma -> Syntax.Term -> Syntax.Term
concreteTerm s (Syntax.ApplyTerm m t1 t2)       = Syntax.ApplyTerm (concreteType s m) (concreteTerm s t1) (concreteTerm s t2)
concreteTerm s (Syntax.AscribeTerm p t ty)      = Syntax.AscribeTerm p (concreteTerm s t) ty
concreteTerm s (Syntax.BindTerm m p t1 t2)      = Syntax.BindTerm (concreteType s m) p (concreteTerm s t1) (concreteTerm s t2)
concreteTerm s (Syntax.CaseTerm m t rs)         = Syntax.CaseTerm (concreteType s m) (concreteTerm s t) (map (concreteRule s) rs)
concreteTerm s (Syntax.ForTerm m1s m2 ps t1 t2) = Syntax.ForTerm (map (concreteType s) m1s) (concreteType s m2) ps (concreteTerm s t1) (concreteTerm s t2)
concreteTerm s (Syntax.VariableTerm p x)        = Syntax.VariableTerm p x
concreteTerm s (Syntax.SeqTerm t1 t2)           = Syntax.SeqTerm (concreteTerm s t1) (concreteTerm s t2)
concreteTerm s (Syntax.StringTerm p x)          = Syntax.StringTerm p x
concreteTerm s (Syntax.TupleTerm p ms xs)       = Syntax.TupleTerm p (map (concreteType s) ms) (map (concreteTerm s) xs)
concreteTerm s (Syntax.UnitTerm p)              = Syntax.UnitTerm p
concreteTerm s (Syntax.UpperTerm p ts ty x xs)  = Syntax.UpperTerm p (map (concreteType s) ts) (concreteType s ty) x xs


concreteRule :: Sigma -> (Syntax.Pat, Syntax.Term) -> (Syntax.Pat, Syntax.Term)

concreteRule s (p, t) = (p, concreteTerm s t)


-- Replaces any metavariables found in sigma. If the metavariable is not in
-- sigma, it is replaced with ().

concreteType :: Sigma -> Type.Type -> Type.Type

concreteType s (Type.Arrow t1 t2)    = Type.Arrow (concreteType s t1) (concreteType s t2)
concreteType s (Type.Metavariable x) = maybe Type.Unit id (sigmaLookup s x)
concreteType s Type.String           = Type.String
concreteType s (Type.Tuple ts)       = Type.Tuple (map (concreteType s) ts)
concreteType s Type.Unit             = Type.Unit
concreteType s (Type.Variable x)     = Type.Variable x
concreteType s (Type.Variant q)      = Type.Variant (Type.Path (map (\ (Type.Name x tys) -> Type.Name x (map (concreteType s) tys)) (Type.pathNames q)))


isConcreteType :: Type.Type -> Bool

isConcreteType (Type.Arrow t1 t2)    = isConcreteType t1 && isConcreteType t2
isConcreteType (Type.Metavariable x) = False
isConcreteType Type.String           = True
isConcreteType (Type.Tuple ts)       = all isConcreteType ts
isConcreteType Type.Unit             = True
isConcreteType (Type.Variable x)     = True
isConcreteType (Type.Variant q)      = all (\ (Type.Name x tys) -> all isConcreteType tys) (Type.pathNames q)


-- Replaces any metavariables found in sigma. If the metavariable is not in
-- sigma, it is returned.

updateType :: Sigma -> Type.Type -> Type.Type

updateType s (Type.Arrow t1 t2)    = Type.Arrow (updateType s t1) (updateType s t2)
updateType s (Type.Metavariable x) = maybe (Type.Metavariable x) id (sigmaLookup s x)
updateType s Type.String           = Type.String
updateType s (Type.Tuple ts)       = Type.Tuple (map (updateType s) ts)
updateType s Type.Unit             = Type.Unit
updateType s (Type.Variable x)     = Type.Variable x
updateType s (Type.Variant q)      = Type.Variant (Type.Path (map (\ (Type.Name x tys) -> Type.Name x (map (updateType s) tys)) (Type.pathNames q)))


typeCheckPat :: Sigma -> Type.Type -> Syntax.Pat -> Either String Sigma

typeCheckPat s ty (Syntax.AscribePat pos p ty2) =
  case unify s ty (Syntax.typType ty2) of
    Nothing -> errorMsg s pos ty (Syntax.typType ty2)
    Just (ty, s) -> typeCheckPat s ty p

typeCheckPat s ty (Syntax.LowerPat _ x) = Right s

typeCheckPat s ty (Syntax.TuplePat pos tys ps) =
  case unify s ty (Type.Tuple tys) of
    Nothing -> errorMsg s pos ty (Type.Tuple tys)
    Just (Type.Tuple tys, s) ->
      case typeCheckPats s tys ps of
        Left msg -> Left msg
        Right s -> Right s
    Just (_, s) -> unreachable

typeCheckPat s ty Syntax.UnderbarPat =
  Right s

typeCheckPat s ty (Syntax.UnitPat pos) =
  case unify s ty Type.Unit of
    Nothing -> errorMsg s pos ty Type.Unit
    Just (ty, s) -> Right s

typeCheckPat s ty (Syntax.UpperPat pos tys ty2 x ps) =
  case unify s ty ty2 of
    Nothing -> errorMsg s pos ty ty2
    Just (ty, s) -> fmap (const s) (typeCheckPats s tys ps)


typeCheckPats :: Sigma -> [Type.Type] -> [Syntax.Pat] -> Either String Sigma

typeCheckPats s [] [] = Right s

typeCheckPats s (ty:tys) (p:ps) =
  case typeCheckPat s ty p of
    Left msg -> Left msg
    Right s -> typeCheckPats s tys ps

typeCheckPats s _ _ = unreachable


-- We pass in an expected type forward to catch type errors as soon as possible.

typeCheckTerm :: Gamma -> Sigma -> Type.Type -> Syntax.Term -> Either String Sigma

typeCheckTerm g s ty2 (Syntax.ApplyTerm ty1 t1 t2) =
  case typeCheckTerm g s (Type.Arrow ty1 ty2) t1 of
    Left msg -> Left msg
    Right s -> typeCheckTerm g s ty1 t2

typeCheckTerm g s ty (Syntax.AscribeTerm p t ty2) =
  let ty2' = Syntax.typType ty2
   in case unify s ty ty2' of
        Nothing -> errorMsg s p ty ty2'
        Just (ty, s) -> typeCheckTerm g s ty t

typeCheckTerm g s ty (Syntax.BindTerm tyP p t1 t2) =
  case typeCheckPat s tyP p of
    Left msg -> Left msg
    Right s ->
      case typeCheckTerm g s tyP t1 of
        Left msg -> Left msg
        Right s ->
          case gammaWithPat g s p tyP of
            Left msg -> Left msg
            Right g -> typeCheckTerm g s ty t2

typeCheckTerm g s ty (Syntax.ForTerm tyPs ty2 ps t1 t2) =
  case maybe (Right s) (typeCheckPats s tyPs) ps of
    Left msg -> Left msg
    Right s ->
      case typeCheckTerm g s (Type.Arrow (foldr Type.Arrow ty2 tyPs) ty) t1 of
        Left msg -> Left msg
        Right s ->
          case maybe (Right g) (\ ps -> gammaWithPats g s ps tyPs) ps of
            Left msg -> Left msg
            Right g -> typeCheckTerm g s ty2 t2

typeCheckTerm g s ty (Syntax.CaseTerm ty2 t rs) =
  case typeCheckRulePats s ty2 rs of
    Left msg -> Left msg
    Right (ty2, s) ->
      case typeCheckTerm g s ty2 t of
        Left msg -> Left msg
        Right s -> typeCheckRules g s ty ty2 rs
  where typeCheckRulePats s ty [] = Right (ty, s)
        typeCheckRulePats s ty ((p, _) : rs) =
          case typeCheckPat s ty p of
            Left msg -> Left msg
            Right s -> typeCheckRulePats s ty rs
        typeCheckRules g s ty1 ty2 [] = Right s
        typeCheckRules g s ty1 ty2 (r:rs) =
          case typeCheckRule g s ty1 ty2 r of
            Left msg -> Left msg
            Right s -> typeCheckRules g s ty1 ty2 rs
        typeCheckRule g s ty1 ty2 (p, t) =
          case gammaWithPat g s p ty2 of
            Left msg -> Left msg
            Right g -> typeCheckTerm g s ty1 t

typeCheckTerm g s ty (Syntax.SeqTerm t1 t2) =
  case typeCheckTerm g s Type.Unit t1 of
    Left msg -> Left msg
    Right s -> typeCheckTerm g s ty t2

typeCheckTerm g s ty (Syntax.StringTerm p x) =
  case unify s ty Type.String of
    Nothing -> errorMsg s p ty Type.String
    Just (Type.String, s) -> Right s
    Just _ -> unreachable

typeCheckTerm g s ty (Syntax.TupleTerm p ms xs) =
  case unify s ty (Type.Tuple ms) of
    Nothing -> errorMsg s p ty (Type.Tuple ms)
    Just (Type.Tuple tys, s) -> typeCheckTerms g s tys xs
    Just _ -> unreachable

typeCheckTerm g s t (Syntax.UnitTerm p) =
  case unify s t Type.Unit of
    Nothing -> errorMsg s p t Type.Unit
    Just (t, s) -> Right s

typeCheckTerm g s ty (Syntax.UpperTerm p ts ty2 x xs) =
  case unify s ty ty2 of
    Nothing -> errorMsg s p ty ty2
    Just (ty, s) -> Right s

typeCheckTerm g s ty (Syntax.VariableTerm p x) =
  case unify s ty (gammaGet g x) of
    Nothing -> errorMsg s p ty (gammaGet g x)
    Just (ty, s) -> Right s


typeCheckTerms :: Gamma -> Sigma -> [Type.Type] -> [Syntax.Term] -> Either String Sigma

typeCheckTerms g s [] [] = Right s

typeCheckTerms g s (ty:tys) (x:xs) =
  case typeCheckTerm g s ty x of
    Left msg -> Left msg
    Right s -> typeCheckTerms g s tys xs

typeCheckTerms g s _ _ = unreachable


errorMsg :: Sigma -> Syntax.Pos -> Type.Type -> Type.Type -> Either String a

errorMsg s (Syntax.Pos filename line col) t1 t2 =
  Left $ filename ++ ":" ++ show line ++ ":" ++ show col ++ ": " ++ "Type mismatch. Expected type " ++ m1 ++ ". Given type " ++ m2 ++ "."
  where (m1, r) = showType [] $ updateType s t1
        (m2, _) = showType r  $ updateType s t2


-- We keep a stack of metavariables, which is those metavariables already given
-- human-readable names. Names are generated:
--
--   "a?", "b?", ..., "y?", "z?", "a1?", "b1?", ...

showType :: [Type.Metavariable] -> Type.Type -> (String, [Type.Metavariable])

showType r (Type.Arrow t1@(Type.Arrow _ _) t2) =
  let (s1, r')  = showType r  t1
      (s2, r'') = showType r' t2
   in ("(" ++ s1 ++ ")" ++ " ⟶ " ++ s2, r'')

showType r (Type.Arrow t1 t2) =
  let (s1, r')  = showType r  t1
      (s2, r'') = showType r' t2
   in (s1 ++ " ⟶ " ++ s2, r'')

showType r (Type.Metavariable x) = f 0 r
  where f n []                = (c n, [x])
        f n (y:r) | x == y    = (c n, y:r)
                  | otherwise = let (s, r') = f (n + 1) r
                                 in (s, y:r')
        c n             = let (q, r) = quotRem n 26
                           in toEnum (fromEnum 'a' + r) : (if q == 0 then "" else show q) ++ "?"

showType r Type.String = ("String", r)

showType r (Type.Tuple ts) =
  ("(" ++ concat (intersperse ", " xs) ++ ")", r')
  where (xs, r') = showTypes r ts

showType r Type.Unit = ("()", r)

showType r (Type.Variable x) = (x, r)

showType r (Type.Variant q)  = showPath r q

showPath :: [Type.Metavariable] -> Type.Path -> (String, [Type.Metavariable])
showPath r (Type.Path [])     = error "showPath"
showPath r (Type.Path (n:ns)) = foldl f (showName r n) ns -- intersperse "." (map (showName r) (pathNames q))
  where f (s1, r) n = let (s2, r') = showName r n
                       in (s1 ++ "." ++ s2, r')

showName :: [Type.Metavariable] -> Type.Name -> (String, [Type.Metavariable])
showName r (Type.Name s1 [])       = (s1, r)
showName r (Type.Name s1 (ty:tys)) = let (s2, r') = foldl f (showType r ty) tys
                                      in (s1 ++ "⟦" ++ s2 ++ "⟧", r')
  where f (s2, r) ty = let (s3, r') = showType r ty
                        in (s2 ++ ", " ++ s3, r')

showTypes :: [Type.Metavariable] -> [Type.Type] -> ([String], [Type.Metavariable])

showTypes r []     = ([], r)
showTypes r (t:ts) = let (s, r') = showType r t
                         (ss, r'') = showTypes r' ts
                      in (s:ss, r'')

showQual :: [String] -> String
showQual = concat . intersperse "."


-- Attempts to unify two types, returning the new type. Two equal concrete types
-- will unify. A concrete type and a metavariable will record the concrete type
-- in sigma as a constraint.

unify :: MonadPlus m => Sigma -> Type.Type -> Type.Type -> m (Type.Type, Sigma)

unify s (Type.Arrow t1 t2) (Type.Arrow t3 t4) = do
  (t5, s) <- unify s t1 t3
  (t6, s) <- unify s t2 t4
  return (Type.Arrow t5 t6, s)

unify s (Type.Metavariable x1) (Type.Metavariable x2) | x1 == x2 =
  return (Type.Metavariable x1, s)

unify s (Type.Metavariable x1) (Type.Metavariable x2) =
  case (sigmaLookup s x1, sigmaLookup s x2) of
    (Nothing, Nothing) -> return (Type.Metavariable x2, sigmaBind s x1 (Type.Metavariable x2))
    (Nothing, Just t2) -> return (t2, sigmaBind s x1 t2)
    (Just t1, Nothing) -> return (t1, sigmaBind s x2 t1)
    (Just t1, Just t2) -> do (t3, s) <- unify s t1 t2
                             return (t3, sigmaBind (sigmaBind s x1 t3) x2 t3)

unify s (Type.Metavariable x1) t2 =
  case sigmaLookup s x1 of
    Nothing -> return (t2, sigmaBind s x1 t2)
    Just t1 -> do (t3, s) <- unify s t1 t2
                  return (t3, sigmaBind s x1 t3)

unify s t1 (Type.Metavariable x2) =
  unify s (Type.Metavariable x2) t1

unify s Type.String Type.String =
  return (Type.String, s)

unify s (Type.Tuple tys1) (Type.Tuple tys2) = do
  (tys3, s) <- unifys s tys1 tys2
  return (Type.Tuple tys3, s)

unify s Type.Unit Type.Unit =
  return (Type.Unit, s)

unify s (Type.Variable x1) (Type.Variable x2) | x1 == x2 =
  return (Type.Variable x1, s)

unify s (Type.Variant q1) (Type.Variant q2) = do
  (q3, s) <- unifyPath s q1 q2
  return (Type.Variant q3, s)

unify s _ _ = mzero


unifys :: MonadPlus m => Sigma -> [Type.Type] -> [Type.Type] -> m ([Type.Type], Sigma)

unifys s [] [] = return ([], s)

unifys s (t1:t1s) (t2:t2s) = do
  (t3, s) <- unify s t1 t2
  (t3s, s) <- unifys s t1s t2s
  return (t3:t3s, s)

unifys s _ _ = mzero


unifyPath :: MonadPlus m => Sigma -> Type.Path -> Type.Path -> m (Type.Path, Sigma)

unifyPath s (Type.Path n1s) (Type.Path n2s) = do
  (n3s, s) <- unifyNames s n1s n2s
  return (Type.Path n3s, s)


unifyNames :: MonadPlus m => Sigma -> [Type.Name] -> [Type.Name] -> m ([Type.Name], Sigma)

unifyNames s [] [] = return ([], s)

unifyNames s (n1:n1s) (n2:n2s) = do
  (n3, s) <- unifyName s n1 n2
  (n3s, s) <- unifyNames s n1s n2s
  return (n3:n3s, s)

unifyNames s _ _ = mzero


unifyName :: MonadPlus m => Sigma -> Type.Name -> Type.Name -> m (Type.Name, Sigma)

unifyName s (Type.Name x1 ty1s) (Type.Name x2 ty2s) | x1 == x2 = do
  (ty3s, s) <- unifys s ty1s ty2s
  return (Type.Name x1 ty3s, s)

unifyName _ _ _ = mzero


-- Table from metavariables to types.

type Sigma = IntMap Type.Type

sigmaEmpty :: Sigma
sigmaEmpty = IntMap.empty

-- The metavariable may not be in sigma because no constraints have been
-- recorded yet, so we return a maybe type.

sigmaLookup :: Sigma -> Type.Metavariable -> Maybe Type.Type
sigmaLookup s x = IntMap.lookup x s

-- If we are binding an unbound metavariable we must replace the metavariable
-- in the RHS. If we are rebinding an already bound variable, don't need to do
-- that because the bound variable will not appear in the RHS.

sigmaBind :: Sigma -> Type.Metavariable -> Type.Type -> Sigma
sigmaBind s x ty =
  case IntMap.lookup x s of
    Nothing -> IntMap.insert x ty (IntMap.map (Type.replace x ty) s)
    Just _ -> IntMap.insert x ty s


-- Table from local variable names to concrete types.

type Gamma = [(String, Type.Type)]

gammaEmpty :: Gamma
gammaEmpty = []

gammaBind :: Gamma -> String -> Type.Type -> Gamma
gammaBind g x ty = (x, ty) : g

gammaGet :: Gamma -> String -> Type.Type
gammaGet g x = maybe (error "Compiler.TypeChecker.gammaGet") id (lookup x g)


unreachable :: a
unreachable = error "unreachable"
