-- Unbound value variables are detected by the parser.
--
-- Substitions only work for modules and not units because it doesn't really
-- matter how long a path to a unit is and you can always substituto to the
-- parent module.

-- Think about whether we must do an arity check for paths. We must check for
-- all paths except paths to functions in a function body.

-- Do we check that constructors in bindings are singleton types?
-- Should we check constructor arity in the type checker?
-- How should we check completeness of case terms?
-- Make sure substitutions work properly when looking up declarations.

module Compiler.SyntaxChecker where

import Control.Monad (forM_, when, unless)
import Data.Either ()

import qualified Compiler.Type as Type
import qualified Compiler.Syntax as Syntax

-- Either returns nothing of there were no errors or returns the error string.

syntaxCheckProgram :: Syntax.Program -> Maybe String
syntaxCheckProgram p = run m
  where m = programCheck p

programCheck :: Syntax.Program -> M ()
programCheck (Syntax.Program decs) = withDecs decs (mapM_ checkDec decs)

checkDec :: Syntax.Dec -> M ()
checkDec dec =
  case dec of
    Syntax.FunDec pos _ _ s1 vs ps ty t -> do
      checkIfFunctionNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      withTypeVariables vs $ do
        checkPats ps
        checkType ty
        checkTerm t
    Syntax.ModDec pos s1 vs decs -> do
      checkIfModuleNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      withTypeVariables vs $
        withDecs decs $
          mapM_ checkDec decs
    Syntax.NewDec pos _ s1 vs q -> do
      checkIfModuleNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      withTypeVariables vs $
        checkIfPathIsValidUnit q
    Syntax.SubDec pos _ s1 vs q -> do
      checkIfModuleNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      checkIfAllTypeVariablesAreFoundInPath pos q vs
      withTypeVariables vs $
        checkIfPathIsValidModule q
    Syntax.SumDec pos _ s1 vs cs -> do
      checkIfTypeNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      withTypeVariables vs $
        withSomething $
          mapM_ checkConstructor cs
    Syntax.UnitDec pos s1 vs decs -> do
      checkIfModuleNameIsAlreadyUsed pos s1
      checkIfTypeVariablesAreUsedMoreThanOnce pos vs
      checkIfTypeVariablesShadow pos vs
      withTypeVariables vs $
        withDecs decs $
          mapM_ checkDec decs

checkType :: Syntax.Type -> M ()
checkType ty =
  case ty of
    Syntax.ArrowType ty1 ty2 -> do
      checkType ty1
      checkType ty2
    Syntax.LowerType pos s -> do
      vs <- look boundTypeVariables
      unless (elem s vs) $
        syntaxErrorLine pos $ "Type variable name " ++ s ++ " is unbound."
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
      checkIfValueVariableIsUsedMultipleTimes pos x
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

checkIfFunctionNameIsAlreadyUsed :: Syntax.Pos -> String -> M ()
checkIfFunctionNameIsAlreadyUsed pos1 s1 = do
  s2s <- get functionNames
  case lookup s1 s2s of
    Just pos2 -> syntaxErrorLine pos1 $ "Function name " ++ s1 ++ " declared previously " ++ relativePosition pos1 pos2 ++ "."
    Nothing -> set (\ s -> s {functionNames = (s1, pos1) : s2s})

checkIfTypeNameIsAlreadyUsed :: Syntax.Pos -> String -> M ()
checkIfTypeNameIsAlreadyUsed pos1 s1 = do
  s2s <- get typeNames
  case lookup s1 s2s of
    Just pos2 -> syntaxErrorLine pos1 $ "Type name " ++ s1 ++ " declared previously " ++ relativePosition pos1 pos2 ++ "."
    Nothing -> set (\ s -> s {typeNames = (s1, pos1) : s2s})

checkIfModuleNameIsAlreadyUsed :: Syntax.Pos -> String -> M ()
checkIfModuleNameIsAlreadyUsed pos1 s1 = do
  s2s <- get moduleNames
  case lookup s1 s2s of
    Just pos2 -> syntaxErrorLine pos1 $ "Module name " ++ s1 ++ " declared previously " ++ relativePosition pos1 pos2 ++ "."
    Nothing -> set (\ s -> s {moduleNames = (s1, pos1) : s2s})

checkIfTypeVariablesAreUsedMoreThanOnce :: Syntax.Pos -> [String] -> M ()
checkIfTypeVariablesAreUsedMoreThanOnce pos vs = f vs []
  where f [] xs = return ()
        f (v:vs) xs = do
          when (elem v xs) $
            syntaxErrorLine pos $ "Type variable name " ++ v ++ " used more than once."
          f vs (v:xs)

checkIfTypeVariablesShadow :: Syntax.Pos -> [String] -> M ()
checkIfTypeVariablesShadow pos v1s = do
  v2s <- look boundTypeVariables
  forM_ v1s $ \ v1 ->
    when (elem v1 v2s) $
      syntaxErrorLine pos $ "Type variable name " ++ v1 ++ " shadows previous type variable."

withTypeVariables :: [String] -> M a -> M a
withTypeVariables vs m =
  with (\ l -> l {boundTypeVariables = vs ++ boundTypeVariables l}) m

-- For sub declarations every type variable must be found in the path so we can
-- replace the substitution without losing any information.
checkIfAllTypeVariablesAreFoundInPath ::  Syntax.Pos -> Syntax.Path -> [String] -> M ()
checkIfAllTypeVariablesAreFoundInPath pos q vs = forM_ vs (checkIfTypeVariableIsFoundInPath pos q)

checkIfTypeVariableIsFoundInPath :: Syntax.Pos -> Syntax.Path -> String -> M ()
checkIfTypeVariableIsFoundInPath pos q v =
  if isTypeVariableFoundInPath v q
    then return ()
    else syntaxErrorLine pos $ "Type variable name " ++ v ++ " is unused."

isTypeVariableFoundInPath :: String -> Syntax.Path -> Bool
isTypeVariableFoundInPath v q = or (map (isTypeVariableFoundInName v) q)

isTypeVariableFoundInName :: String -> Syntax.Name -> Bool
isTypeVariableFoundInName v (_, tys) = or (map (isTypeVariableFoundInType v) tys)

isTypeVariableFoundInType :: String -> Syntax.Type -> Bool
isTypeVariableFoundInType v ty =
  case ty of
    Syntax.ArrowType ty1 ty2 -> or [isTypeVariableFoundInType v ty1, isTypeVariableFoundInType v ty1]
    Syntax.LowerType _ s -> v == s
    Syntax.TupleType tys -> or (map (isTypeVariableFoundInType v) tys)
    Syntax.UnitType _ -> False
    Syntax.UpperType _ q -> isTypeVariableFoundInPath v q

-- These search the enviroment for the declaration and check against it.

checkIfPathIsValidConstructor :: Syntax.Path -> M ()
checkIfPathIsValidConstructor q = later

checkIfPathIsValidFun :: Syntax.Path -> M ()
checkIfPathIsValidFun q =
  case q of
    [] -> unreachable "checkIfPathIsValidFun"
    [n] -> checkIfNameIsValidFun n
    (n:ns) -> checkIfComplexPathIsValidFun n ns

checkIfComplexPathIsValidFun :: Syntax.Name -> [Syntax.Name] -> M ()
checkIfComplexPathIsValidFun n ns = later

inModuleWithName :: Syntax.Name -> M () -> M ()
inModuleWithName n m = later

inModuleWithField :: Syntax.Name -> M () -> M ()
inModuleWithField n m = later

isNameValidModule :: Syntax.Name -> Syntax.Dec -> M () -> Maybe (M ())
isNameValidModule (s1, v1s) dec m =
  case dec of
    Syntax.ModDec _ s2 v2s decs | s1 == s2 -> Just $ do
      when (length v1s /= 0) $ do
        when (length v1s /= length v2s) $ do
          fail $ "module type arity mismatch"
      withDecs decs m
    Syntax.NewDec _ _ s2 v2s q | s1 == s2 -> Just $
      inUnitWithPath q m
    Syntax.UnitDec _ s2 _ _ | s1 == s2 -> Just $
      fail "path to unit"
    _ -> Nothing

inUnitWithPath :: Syntax.Path -> M () -> M ()
inUnitWithPath _ _ = later

checkIfNameIsValidFun :: Syntax.Name -> M ()
checkIfNameIsValidFun n = do
  r <- look envStack
  case r of
    -- Check builtin functions.
    [] -> later
    (decs:r) -> do
      case search (isNameValidFun n) decs of
        Nothing -> with (\ l -> l {envStack = r}) (checkIfNameIsValidFun n)
        Just m -> m

isNameValidFun :: Syntax.Name -> Syntax.Dec -> Maybe (M ())
isNameValidFun (s1, v1s) dec =
  case dec of
    Syntax.FunDec _ _ _ s2 v2s _ _ _ | s1 == s2 -> Just $ do
      when (length v1s /= 0) $ do
        when (length v1s /= length v2s) $ do
          fail $ "function type arity mismatch"
    Syntax.SumDec _ _ _ v2s cs ->
      search (isNameValidConstructor (s1, v1s) v2s) cs
    _ -> Nothing

isNameValidConstructor :: Syntax.Name -> [String] -> (Syntax.Pos, [Type.Type], String, [Syntax.Type]) -> Maybe (M ())
isNameValidConstructor (s1, v1s) v2s c =
  case c of
    (pos, _, s2, tys) | s1 == s2 -> Just $ do
      when (length v1s /= 0) $ do
        when (length v1s /= length v2s) $ do
          fail $ "function type arity mismatch"
    _ -> Nothing

checkIfPathIsValidType :: Syntax.Path -> M ()
checkIfPathIsValidType q = later

checkIfPathIsValidUnit :: Syntax.Path -> M ()
checkIfPathIsValidUnit q = later

checkIfPathIsValidModule :: Syntax.Path -> M ()
checkIfPathIsValidModule q = later

checkConstructor :: (Syntax.Pos, [Type.Type], String, [Syntax.Type]) -> M ()
checkConstructor (pos, _, s1, tys) = do
  checkIfFunctionNameIsAlreadyUsed pos s1
  mapM_ checkType tys

checkIfValueVariableIsUsedMultipleTimes :: Syntax.Pos -> String -> M ()
checkIfValueVariableIsUsedMultipleTimes pos v = do
  vs <- get valueVariables
  when (elem v vs) $
    syntaxErrorLine pos $ "Variable name " ++ v ++ " used more than once in pattern."
  set (\ s -> s {valueVariables = (v:vs)})

withDecs :: [Syntax.Dec] -> M a -> M a
withDecs decs m = do
  s <- get id
  set (\ _ -> emptyState)
  x <- with (\ l -> l {envStack = decs : envStack l}) m
  set (\ _ -> s)
  return x

withSomething :: M a -> M a
withSomething m = m

withEmptyVariables :: M a -> M a
withEmptyVariables m = do
  vs <- get valueVariables
  x <- m
  set (\ s -> s {valueVariables = vs})
  return x

run :: M () -> Maybe String
run m = runM m emptyLook (\ x _ -> Nothing) emptyState

emptyLook :: Look
emptyLook = Look
  { envStack = []
  , boundTypeVariables = []
  }

emptyState :: State
emptyState = State
  { valueVariables = []
  , moduleNames = []
  , typeNames = []
  , functionNames = []
  }

newtype M a = M { runM :: Look -> (a -> State -> Maybe String) -> State -> Maybe String }

data State = State
 { valueVariables :: [String]
 , moduleNames :: [(String, Syntax.Pos)]
 , typeNames :: [(String, Syntax.Pos)]
   -- Name and line of function.
 , functionNames :: [(String, Syntax.Pos)]
 }

data Look = Look
 { envStack :: [[Syntax.Dec]]
 , boundTypeVariables :: [String]
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

--------------------------------------------------------------------------------
-- Error Messages
--------------------------------------------------------------------------------

nameString :: Syntax.Name -> String
nameString (s, vs) = todo "nameString"

pathString :: Syntax.Path -> String
pathString q =
  case q of
    [] -> unreachable "pathString"
    [n] -> nameString n
    (n:ns) -> nameString n ++ concat (map (\ n -> "." ++ nameString n) ns)

bar01 :: Int -> Syntax.Name -> String
bar01 line n = syntaxError line $ "Module " ++ nameString n ++ " not found."

bar02 :: Int -> Syntax.Name -> Syntax.Path -> String
bar02 line n q = syntaxError line $ "Module " ++ nameString n ++ " at " ++ pathString q ++ " not found."

syntaxError :: Int -> String -> String
syntaxError line s = todo "syntaxError"

syntaxErrorLine :: Syntax.Pos -> String -> M a
syntaxErrorLine (Syntax.Pos filename line col) msg =
  fail $ filename ++ ":" ++ show line ++ ": Syntax error: " ++ msg

relativePosition :: Syntax.Pos -> Syntax.Pos -> String
relativePosition (Syntax.Pos filename1 line1 col1) (Syntax.Pos filename2 line2 col2) =
  "on line " ++ show line2 ++ if filename1 == filename2 then "" else (" of file " ++ filename2)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

later :: M ()
later = return ()

search :: (a -> Maybe b) -> [a] -> Maybe b
search f [] = Nothing
search f (x:xs) = maybe (search f xs) Just (f x)

todo :: String -> a
todo s = error $ "todo: SyntaxChecker." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: SyntaxChecker." ++ s
