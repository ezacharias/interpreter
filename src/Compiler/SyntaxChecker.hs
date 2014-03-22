-- Do we check that lower-case variable are bound even though the parser does this?
-- Do we check that constructors in bindings are singleton types?
-- Should we check constructor arity in the type checker?
-- Should we allow substitutions of units?
-- Should we check type variable shadowing in parser?
-- What else should we check in the parser?
-- How should we check completeness of case terms?
-- Make sure substitutions work properly when looking up declarations.

module Compiler.SyntaxChecker where

import Control.Monad (forM_, when)
import Data.Either ()

import qualified Compiler.Type as Type
import qualified Compiler.Syntax as Syntax

-- Either returns nothing of there were no errors or returns the error string.

syntaxCheckProgram :: Syntax.Program -> Maybe String
syntaxCheckProgram p = run m
  where m = programCheck p

maybeEither :: Either a () -> Maybe a
maybeEither (Left x)   = Just x
maybeEither (Right ()) = Nothing

programCheck :: Syntax.Program -> M ()
programCheck (Syntax.Program decs) = withDecs decs (mapM_ checkDec decs)

checkDec :: Syntax.Dec -> M ()
checkDec dec =
  case dec of
    Syntax.FunDec _ _ _ s1 vs ps ty t -> do
      checkIfFunctionNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      checkType ty
      checkTerm t
    Syntax.ModDec pos s1 vs decs -> do
      checkIfModuleNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      withDecs decs $
        mapM_ checkDec decs
    Syntax.NewDec pos _ s1 vs q -> do
      checkIfModuleNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      checkIfPathIsValidUnit q
    Syntax.SubDec pos _ s1 vs q -> do
      checkIfModuleNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      checkIfAllTypeVariablesAreFoundInPath q vs
      checkIfPathIsValidModule q
    Syntax.SumDec pos _ s1 vs cs -> do
      checkIfTypeNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      withSomething $
        mapM_ checkConstructor cs
    Syntax.UnitDec pos s1 vs decs -> do
      checkIfModuleNameIsAlreadyUsed s1
      checkIfTypeVariablesAreUsedMoreThanOnce vs
      -- checkIfTypeVariablesShadow vs
      withDecs decs $
        mapM_ checkDec decs

checkType :: Syntax.Type -> M ()
checkType ty =
  case ty of
    Syntax.ArrowType ty1 ty2 -> do
      checkType ty1
      checkType ty2
    Syntax.LowerType s ->
      -- Whether variables are bound is checked by the parser.
      return ()
    Syntax.TupleType tys ->
      mapM_ checkType tys
    Syntax.UnitType pos ->
      return ()
    Syntax.UpperType pos q ->
      checkIfPathIsValidType q

checkTerm :: Syntax.Term -> M ()
checkTerm t =
  case t of
    Syntax.ApplyTerm _ t1 t2 -> do
      checkTerm t1
      checkTerm t2
    Syntax.AscribeTerm pos _ t ty -> do
      checkTerm t
      checkType ty
    Syntax.BindTerm _ p t1 t2 -> do
      checkPat p
      checkTerm t1
      checkTerm t2
    Syntax.CaseTerm _ t rs -> do
      checkTerm t
      forM_ rs checkRule
    Syntax.ForTerm _ _ ps t1 t2 -> do
      checkPats ps
      checkTerm t1
      checkTerm t2
    Syntax.SeqTerm t1 t2 -> do
      checkTerm t1
      checkTerm t2
    Syntax.StringTerm pos s ->
      return ()
    Syntax.TupleTerm pos _ ts ->
      mapM_ checkTerm ts
    Syntax.UnitTerm pos ->
      return ()
    Syntax.UpperTerm pos _ _ q ->
      checkIfPathIsValidFun q
    Syntax.VariableTerm pos string ->
      -- Whether variables are bound is checked by the parser.
      return ()

checkRule :: Syntax.Rule -> M ()
checkRule (p, t) = do
  checkPat p
  checkTerm t

checkPat :: Syntax.Pat -> M ()
checkPat p = checkPats [p]

-- We much check that no variable in the pattern is used more than once.
checkPats :: [Syntax.Pat] -> M ()
checkPats ps =
  withEmptyVariables $
    forM_ ps reallyCheckPat

reallyCheckPat :: Syntax.Pat -> M ()
reallyCheckPat p =
  case p of
    Syntax.AscribePat pos _ p ty -> do
      reallyCheckPat p
      checkType ty
    Syntax.LowerPat pos x ->
      checkIfValueVariableIsUsedMultipleTimes x
    Syntax.TuplePat pos _ ps ->
      forM_ ps reallyCheckPat
    Syntax.UnderbarPat ->
      return ()
    Syntax.UnitPat pos ->
      return ()
    Syntax.UpperPat pos _ _ _ q ps -> do
      checkIfPathIsValidConstructor q
      forM_ ps reallyCheckPat

-- These both check if the declaration is in the namespace at the current level
-- and add it to the namespace.

checkIfFunctionNameIsAlreadyUsed :: String -> M ()
checkIfFunctionNameIsAlreadyUsed s1 = do
  s2s <- get functionNames
  case elem s1 s2s of
    True -> fail $ "function name used: " ++ s1
    False -> set (\ s -> s {functionNames = s1 : s2s})

checkIfTypeNameIsAlreadyUsed :: String -> M ()
checkIfTypeNameIsAlreadyUsed s1 = do
  s2s <- get typeNames
  case elem s1 s2s of
    True -> fail $ "type name used: " ++ s1
    False -> set (\ s -> s {typeNames = s1 : s2s})

checkIfModuleNameIsAlreadyUsed :: String -> M ()
checkIfModuleNameIsAlreadyUsed s1 = do
  s2s <- get moduleNames
  case elem s1 s2s of
    True -> fail $ "module name used: " ++ s1
    False -> set (\ s -> s {moduleNames = s1 : s2s})

checkIfTypeVariablesAreUsedMoreThanOnce :: [String] -> M ()
checkIfTypeVariablesAreUsedMoreThanOnce vs = f vs []
  where f [] xs = return ()
        f (v:vs) xs = do
          when (elem v xs) $
            fail $ "type variable used more than once: " ++ v
          f vs (v:xs)

{-
checkIfTypeVariablesShadow :: [String] -> M ()
checkIfTypeVariablesShadow v1s = do
  v2s <- look typeVariables
  forM_ v1s $ \ v1 ->
    when (elem v1 v2s) $
      fail $ "type variable shadows" ++ v1

withTypeVariables :: [String] -> M a -> M a
withTypeVariables vs m =
  with (\ l -> l {typeVariables = vs ++ typeVariables l}) m
-}

-- For sub declarations every type variable must be found in the path so we can
-- replace the substitution without losing any information.
checkIfAllTypeVariablesAreFoundInPath ::  Syntax.Path -> [String] -> M ()
checkIfAllTypeVariablesAreFoundInPath q vs = forM_ vs (checkIfTypeVariableIsFoundInPath q)

checkIfTypeVariableIsFoundInPath :: Syntax.Path -> String -> M ()
checkIfTypeVariableIsFoundInPath q v =
  if isTypeVariableFoundInPath v q
    then return ()
    else fail $ "type variable not bound: " ++ v

isTypeVariableFoundInPath :: String -> Syntax.Path -> Bool
isTypeVariableFoundInPath v q = or (map (isTypeVariableFoundInName v) q)

isTypeVariableFoundInName :: String -> Syntax.Name -> Bool
isTypeVariableFoundInName v (_, tys) = or (map (isTypeVariableFoundInType v) tys)

isTypeVariableFoundInType :: String -> Syntax.Type -> Bool
isTypeVariableFoundInType v ty =
  case ty of
    Syntax.ArrowType ty1 ty2 -> or [isTypeVariableFoundInType v ty1, isTypeVariableFoundInType v ty1]
    Syntax.LowerType s -> v == s
    Syntax.TupleType tys -> or (map (isTypeVariableFoundInType v) tys)
    Syntax.UnitType _ -> False
    Syntax.UpperType _ q -> isTypeVariableFoundInPath v q

-- These search the enviroment for the declaration and check against it.

checkIfPathIsValidConstructor :: Syntax.Path -> M ()
checkIfPathIsValidConstructor q = later

checkIfPathIsValidFun :: Syntax.Path -> M ()
checkIfPathIsValidFun q = later

checkIfPathIsValidType :: Syntax.Path -> M ()
checkIfPathIsValidType q = later

checkIfPathIsValidUnit :: Syntax.Path -> M ()
checkIfPathIsValidUnit q = later

checkIfPathIsValidModule :: Syntax.Path -> M ()
checkIfPathIsValidModule q = later

checkConstructor :: (Syntax.Pos, [Type.Type], String, [Syntax.Type]) -> M ()
checkConstructor (pos, _, s1, tys) = do
  checkIfFunctionNameIsAlreadyUsed s1
  mapM_ checkType tys

checkIfValueVariableIsUsedMultipleTimes :: String -> M ()
checkIfValueVariableIsUsedMultipleTimes v = do
  vs <- get valueVariables
  when (elem v vs) $
    fail $ "variable used more than once: " ++ v
  set (\ s -> s {valueVariables = (v:vs)})

withDecs :: [Syntax.Dec] -> M a -> M a
withDecs decs m =
  with (\ l -> l {envStack = decs : envStack l}) m

withSomething :: M a -> M a
withSomething m = m

withEmptyVariables :: M a -> M a
withEmptyVariables m = do
  vs <- get valueVariables
  x <- m
  set (\ s -> s {valueVariables = vs})
  return x

run :: M () -> Maybe String
run m = runM m l (\ x _ -> Nothing) s
  where s = State
              { valueVariables = []
              , moduleNames = []
              , typeNames = []
              , functionNames = []
              }
        l = Look
              { -- typeVariables = []
                envStack = []
              }

newtype M a = M { runM :: Look -> (a -> State -> Maybe String) -> State -> Maybe String }

data State = State
 { valueVariables :: [String]
 , moduleNames :: [String]
 , typeNames :: [String]
 , functionNames :: [String]
 }

data Look = Look
 { -- typeVariables :: [String]
   envStack :: [[Syntax.Dec]]
 }

instance Monad M where
  return x = M (\ o k -> k x)
  m >>= f = M (\ o k -> runM m o (\ x -> runM (f x) o k))
  fail s = M (\ o k d -> Just s)

get :: (State -> a) -> M a
get f = M (\ o k d -> k (f d) d)

set :: (State -> State) -> M ()
set f = M (\ o k d -> k () (f d))

look :: (Look -> a) -> M a
look f = M (\ o k d -> k (f o) d)

with :: (Look -> Look) -> M a -> M a
with f m = M (\ o k d -> runM m (f o) k d)

-- Utilities

later :: M ()
later = return ()

todo :: String -> a
todo s = error $ "todo: SyntaxChecker." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: SyntaxChecker." ++ s
