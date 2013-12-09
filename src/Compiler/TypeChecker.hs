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

import           Control.Monad
import           Control.Monad.Instances ()
import           Data.IntMap             (IntMap)
import qualified Data.IntMap             as IntMap
import           Data.List               (intersperse)

import qualified Compiler.Syntax         as Syntax
import qualified Compiler.Type           as Type

inferProgram :: Syntax.Program -> Either String Syntax.Program
inferProgram (Syntax.Program xs) = liftM Syntax.Program (mapM inferDec xs)

inferDec :: Syntax.Dec -> Either String Syntax.Dec
inferDec (Syntax.FunDec pos s ss ps ty t) = do t' <- withPats tys' ps $
                                                       inferTerm gammaEmpty sigmaEmpty ty' t
                                               return $ Syntax.FunDec pos s ss ps ty t'
  where tys' = map Syntax.patType ps
        ty' = Syntax.typType ty

-- | Metavariables
type Sigma = IntMap Type.Type

-- | Local variables
type Gamma = [(String, Type.Type)]

withPats :: [Type.Type] -> [Syntax.Pat] -> Either String Syntax.Term -> Either String Syntax.Term
withPats [] [] m = m
withPats (t:ts) (p:ps) m = withPat t p (withPats ts ps m)
withPats _ _ _ = error "Compiler.TypeChecker.withPats: impossible"

withPat :: Type.Type -> Syntax.Pat -> Either String Syntax.Term -> Either String Syntax.Term
withPat _ (Syntax.UnitPat _) m = m

-- The first thing we do is run typeCheckTerm, which gets us the table of
-- metavariables. We then run updateTerm, which uses the table to replace
-- metavariables with concrete types.

inferTerm :: Gamma -> Sigma -> Type.Type -> Syntax.Term -> Either String Syntax.Term
inferTerm g s ty t = do (ty, s) <- typeCheckTerm g s ty t
                        return $ updateTerm s t

-- | Replaces all metavariables in the syntax with concrete types.

updateTerm :: Sigma -> Syntax.Term -> Syntax.Term
updateTerm s (Syntax.ApplyTerm m t1 t2)   = Syntax.ApplyTerm (updateType s m) (updateTerm s t1) (updateTerm s t2)
updateTerm s (Syntax.VariableTerm p x)    = Syntax.VariableTerm p x
updateTerm s (Syntax.TupleTerm p ms xs)   = Syntax.TupleTerm p (map (updateType s) ms) (map (updateTerm s) xs)
updateTerm s (Syntax.UnitTerm p)          = Syntax.UnitTerm p
updateTerm s (Syntax.UpperTerm p ts ty x) = Syntax.UpperTerm p (map (updateType s) ts) (updateType s ty) x

updateType :: Sigma -> Type.Type -> Type.Type
updateType s (Type.Arrow t1 t2)    = Type.Arrow (updateType s t1) (updateType s t2)
updateType s (Type.Metavariable x) = sigmaGet s x
updateType s (Type.Tuple ts)       = Type.Tuple (map (updateType s) ts)
updateType s Type.Unit             = Type.Unit
updateType s (Type.Variable x)     = Type.Variable x
updateType s (Type.Variant x ts)   = Type.Variant x (map (updateType s) ts)

-- If a metaviable is not in sigma, it means there are no constraints on the
-- metavariable, so we give it type Unit.

sigmaGet :: Sigma -> Type.Metavariable -> Type.Type
sigmaGet s m = maybe Type.Unit id (sigmaLookup s m)

gammaGet :: Gamma -> String -> Type.Type
gammaGet g x = maybe (error "Compiler.TypeChecker.gammaGet") id (lookup x g)

-- We pass in an expected type forward to catch type errors as soon as possible.

typeCheckTerm :: Gamma -> Sigma -> Type.Type -> Syntax.Term -> Either String (Type.Type, Sigma)

typeCheckTerm g s ty (Syntax.ApplyTerm m t1 t2) =
  case typeCheckTerm g s (Type.Arrow m ty) t1 of
    Left msg -> Left msg
    Right (Type.Arrow ty1 ty2, s) ->
      case typeCheckTerm g s ty1 t2 of
        Left msg -> Left msg
        Right (ty1, s) -> return (updateType s ty2, s)
    Right (_, s) -> unreachable

typeCheckTerm g s ty (Syntax.TupleTerm p ms xs) =
  case unify s ty (Type.Tuple ms) of
    Nothing -> errorMsg p ty (Type.Tuple ms)
    Just (Type.Tuple ts, s) ->
      case typeCheckTerms g s ts xs of
        Left msg -> Left msg
        Right (tys, s) -> Right (Type.Tuple tys, s)
    Just _ -> unreachable

typeCheckTerm g s t (Syntax.UnitTerm p) =
  case unify s t Type.Unit of
    Nothing -> errorMsg p t Type.Unit
    Just (t, s) -> Right (t, s)

typeCheckTerm g s ty (Syntax.UpperTerm p ts ty2 x) =
  case unify s ty ty2 of
    Nothing -> errorMsg p ty ty2
    Just (ty, s) -> Right (ty, s)

typeCheckTerm g s ty (Syntax.VariableTerm p x) =
  case unify s ty (gammaGet g x) of
    Nothing -> errorMsg p ty (gammaGet g x)
    Just (ty, s) -> Right (ty, s)

typeCheckTerms :: Gamma -> Sigma -> [Type.Type] -> [Syntax.Term] -> Either String ([Type.Type], Sigma)
typeCheckTerms g s [] [] = Right ([], s)
typeCheckTerms g s (ty:tys) (x:xs) =
  case typeCheckTerm g s ty x of
    Left msg -> Left msg
    Right (ty, s) ->
      case typeCheckTerms g s tys xs of
        Left msg -> Left msg
        Right (tys, s) -> Right (ty:tys, s)
typeCheckTerms g s _ _ = unreachable

errorMsg :: Syntax.Pos -> Type.Type -> Type.Type -> Either String a
errorMsg (Syntax.Pos filename line col) t1 t2 =
  Left $ filename ++ ":" ++ show line ++ ":" ++ show col ++ ": " ++ "Type mismatch. Expected " ++ s1 ++ ". Given " ++ s2 ++ "."
  where (s1, r) = showType [] t1
        (s2, _) = showType r  t2

-- This does not work correctly with variables because metavariables may have the same name.

showType :: [Type.Metavariable] -> Type.Type -> (String, [Type.Metavariable])
showType r (Type.Arrow t1 t2) = let (s1, r')  = showType r  t1
                                    (s2, r'') = showType r' t2
                                 in (s1 ++ " -> " ++ s2, r'')
showType r (Type.Metavariable x) = f 0 r
 where
  f n []                = (c n, [x])
  f n (y:r) | x == y    = (c n, y:r)
            | otherwise = let (s, r') = f (n + 1) r
                           in (s, y:r)
  c n | n < 26    = [toEnum (fromEnum 'a' + n)]
      | otherwise = error "Compiler.TypeChecker.showType"
showType r (Type.Tuple ts) = ("(" ++ concat (intersperse ", " xs) ++ ")", r')
  where (xs, r') = showTypes r ts
showType r Type.Unit = ("()", r)
showType r (Type.Variable x) = (x, r)
showType r (Type.Variant s ts) = let (ss, r') = showTypes r ts
                                  in (s ++ concat ss, r')

showTypes :: [Type.Metavariable] -> [Type.Type] -> ([String], [Type.Metavariable])
showTypes r []     = ([], r)
showTypes r (t:ts) = let (s, r') = showType r t
                         (ss, r'') = showTypes r' ts
                      in (s:ss, r'')

-- We attempt to unify the two types. For example, we may expect a pair
-- of integers. This will match with a pair of metavariables. The function may fail, in which case we
-- report the two original types along with a message saying they did not unify.

-- The basic idea is concrete types unify based on structural equality. Two identical metavariables
-- unify.

unify :: Sigma -> Type.Type -> Type.Type -> Maybe (Type.Type, Sigma)
unify s (Type.Arrow t1 t2) (Type.Arrow t3 t4) =
  do (t5, s) <- unify s t1 t3
     (t6, s) <- unify s t2 t4
     return $ (Type.Arrow t5 t6, s)
unify s (Type.Metavariable x1) (Type.Metavariable x2)
  | x1 == x2  = Just (Type.Metavariable x1, s)
  | otherwise =
      case (sigmaLookup s x1, sigmaLookup s x2) of
        (Nothing, Nothing) -> Just (Type.Metavariable x2, sigmaBind s x1 (Type.Metavariable x2))
        (Nothing, Just t2) -> Just (t2, sigmaBind s x1 t2)
        (Just t1, Nothing) -> Just (t1, sigmaBind s x2 t1)
        (Just t1, Just t2) -> case unify s t1 t2 of
                                Nothing -> Nothing
                                Just (t3, s) -> Just (t3, sigmaBind (sigmaBind s x1 t3) x2 t3)
unify s (Type.Metavariable x1) t2 =
  do t1 <- sigmaLookup s x1
     (t3, s) <- unify s t1 t2
     return (t3, sigmaBind s x1 t3)
unify s t1 (Type.Metavariable x2) =
  unify s (Type.Metavariable x2) t1
unify s Type.Unit Type.Unit =
  Just (Type.Unit, s)
unify s (Type.Variable x1) (Type.Variable x2) | x1 == x2 = return (Type.Variable x1, s)
unify s (Type.Variant x1 t1s) (Type.Variant x2 t2s) | x1 == x2 =
  do (t3s, s) <- unifys s t1s t2s
     return $ (Type.Variant x1 t3s, s)
unify s _ _ = Nothing

unifys :: Sigma -> [Type.Type] -> [Type.Type] -> Maybe ([Type.Type], Sigma)
unifys s [] [] = return ([], s)
unifys s (t1:t1s) (t2:t2s) = do (t3, s) <- unify s t1 t2
                                (t3s, s) <- unifys s t1s t2s
                                return (t3:t3s, s)
unifys s _ _ = Nothing


sigmaEmpty :: Sigma
sigmaEmpty = IntMap.empty

sigmaLookup :: Sigma -> Type.Metavariable -> Maybe Type.Type
sigmaLookup s x = IntMap.lookup x s

-- If we are binding an unbound metavariable we must replace the metavariable
-- in the RHS. If we are rebinding an already bound variable, don't need to do
-- that.

sigmaBind :: Sigma -> Type.Metavariable -> Type.Type -> Sigma
sigmaBind s x ty =
  case IntMap.lookup x s of
    Nothing -> IntMap.insert x ty (IntMap.map (Type.replace x ty) s)
    Just _ -> IntMap.insert x ty s

gammaEmpty :: Gamma
gammaEmpty = []

unreachable :: a
unreachable = error "unreachable"
