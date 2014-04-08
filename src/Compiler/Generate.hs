module Compiler.Generate where

import           Control.Monad   (forM_)
import qualified Data.IntMap     as IntMap
import           Data.Maybe      (fromMaybe)

import qualified Compiler.Direct as Direct

generateProgram :: Direct.Program -> M ()
generateProgram (Direct.Program _ x1s d1) = do
  let x2s = IntMap.assocs x1s
  forM_ x2s generateFunctionPrototype
  put ""
  forM_ x2s generateFun
  generateMain d1

generateFunctionPrototype :: (Direct.Ident, Direct.Fun) -> M ()
generateFunctionPrototype (d, _) = reallyGenerateFunctionPrototype d

reallyGenerateFunctionPrototype :: Direct.Ident -> M ()
reallyGenerateFunctionPrototype d =
  put $ "static void f" ++ show d ++ "(state *);"

generateMain :: Direct.Ident -> M ()
generateMain d1 = do
  n1 <- getMaxArgumentsSize
  put $ "main() {"
  indent $ do
    put $ "state *s = (state *)malloc(sizeof(state));"
    put $ "s->function = f" ++ show d1 ++ ";"
    put $ "s->arguments = (uint64_t)malloc(sizeof(" ++ show n1 ++ "));"
    put $ "for (;;) {"
    indent $ do
      put $ "switch (s->function(s)) {"
      put $ "case CALL_RETURN_CODE:"
      indent $ do
        put $ "break;"
      put $ "case UNREACHABLE_RETURN_CODE:"
      indent $ do
        put $ "return 1;"
      put $ "}"
    put $ "}"
  put $ "}"

-- We reset the monad state here.
generateFun :: (Direct.Ident, Direct.Fun) -> M ()
generateFun (d, x) = do
  reallyGenerateFun d x
  put $ ""

reallyGenerateFun :: Direct.Ident -> Direct.Fun -> M ()
reallyGenerateFun d1 (Direct.Fun d2s ty1s t1) = do
  put $ "static void f" ++ show d1 ++ "(state *s) {"
  indent $ do
    -- This local points to the argument array.
    d3 <- newLocal
    put $ "uint64_t " ++ d3 ++ " = s->arguments;"
    -- Bind the parameters by loading from the argument array.
    argumentsSize <- putLoads d3 0 d2s ty1s
    -- We keep track of the maximum argument size in bytes because an array of
    -- that size will need to be allocated.
    setMaxArgumentsSize argumentsSize
    -- Generate the body.
    generateTerm t1
  put $ "}"

putLoads :: Local -> Offset -> [Direct.Ident] -> [Direct.Type] -> M Offset
putLoads x1 x2 [] [] = return x2
putLoads x1 x2 (x3:x3s) (x4:x4s) = do x2 <- putLoad x1 x2 x3 x4
                                      putLoads x1 x2 x3s x4s
putLoads _ _ _ _ = unreachable "putLoads"

putLoad :: Local -> Offset -> Direct.Ident -> Direct.Type -> M Offset
putLoad x1 x2 x3 x4 =
  case x4 of
    Direct.StringType -> do
      x5 <- newLocal
      put $ "uint64_t " ++ x5 ++ " = *(uint64_t *)" ++ offsetString x1 x2 ++ ";"
      x6 <- newLocal
      put $ "uint64_t " ++ x6 ++ " = *(uint64_t *)" ++ offsetString x1 (x2 + 8) ++ ";"
      x7 <- newLocal
      put $ "uint64_t " ++ x7 ++ " = *(uint64_t *)" ++ offsetString x1 (x2 + 16) ++ ";"
      setIdentLocals3 x3 (x5, x6, x7)
      setIdentType x3 x4
      return $ x2 + 24
    Direct.SumType _ -> do
      x5 <- newLocal
      put $ "uint64_t " ++ x5 ++ " = *(uint64_t *)" ++ offsetString x1 x2 ++ ";"
      setIdentLocal x3 x5
      setIdentType x3 x4
      return $ x2 + 8
    Direct.TupleType _ -> do
      x5 <- newLocal
      put $ "uint64_t " ++ x5 ++ " = *(uint64_t *)" ++ offsetString x1 x2 ++ ";"
      setIdentLocal x3 x5
      setIdentType x3 x4
      return $ x2 + 8

putStores :: Local -> Offset -> [Direct.Ident] -> [Direct.Type] -> M Offset
putStores x1 x2 [] [] = return x2
putStores x1 x2 (x3:x3s) (x4:x4s) = do x2 <- putStore x1 x2 x3 x4
                                       putStores x1 x2 x3s x4s
putStores _ _ _ _ = unreachable "putStores"

putStore :: Local -> Offset -> Direct.Ident -> Direct.Type -> M Offset
putStore x1 x2 x3 x4 = do
  case x4 of
    Direct.StringType -> do
      (x6, x7, x8) <- getIdentLocals3 x3
      put $ "*(uint64_t *)" ++ offsetString x1  x2       ++ " = " ++ x6 ++ ";"
      put $ "*(uint64_t *)" ++ offsetString x1 (x2 + 8)  ++ " = " ++ x7 ++ ";"
      put $ "*(uint64_t *)" ++ offsetString x1 (x2 + 16) ++ " = " ++ x8 ++ ";"
      return $ x2 + 24
    Direct.TupleType _ -> do
      x6 <- getIdentLocal x3
      put $ "*(uint64_t *)" ++ offsetString x1  x2       ++ " = " ++ x6 ++ ";"
      return $ x2 + 8
    Direct.SumType _ -> do
      x6 <- getIdentLocal x3
      put $ "*(uint64_t *)" ++ offsetString x1  x2       ++ " = " ++ x6 ++ ";"
      return $ x2 + 8

offsetString :: Local -> Offset -> String
offsetString s 0 = s
offsetString s n = "(" ++ s ++ " + " ++ show n ++ ")"

data State = State
 { maxArgumentsSize :: Int
 , resultStrings    :: [String]
 , localCount       :: Int
 , identLocals      :: [(Direct.Ident, [String])]
 , identTypes       :: [(Direct.Ident, Direct.Type)]
 , frontierLocal    :: Local
 }

data Look = Look
 { indentation :: String
 }

newtype M a = M { runM :: Look -> (a -> State -> String) -> State -> String }

instance Monad M where
  return x = M (\ o k -> k x)
  m >>= f = M (\ o k -> runM m o (\ x -> runM (f x) o k))

get :: (State -> a) -> M a
get f = M (\ o k d -> k (f d) d)

set :: (State -> State) -> M ()
set f = M (\ o k d -> k () (f d))

look :: (Look -> a) -> M a
look f = M (\ o k d -> k (f o) d)

with :: (Look -> Look) -> M a -> M a
with f m = M (\ o k d -> runM m (f o) k d)

getMaxArgumentsSize :: M Int
getMaxArgumentsSize = get maxArgumentsSize

setMaxArgumentsSize :: Int -> M ()
setMaxArgumentsSize n1 = do
  n2 <- get maxArgumentsSize
  set (\ s -> s {maxArgumentsSize = max n1 n2})

put :: String -> M ()
put s1 =
  set (\ s -> s {resultStrings = s1:(resultStrings s)})

indent :: M a -> M a
indent m1 =
  with (\ s -> s {indentation = ' ':':':(indentation s)}) m1

type Local = String
type Offset = Int

newLocal :: M String
newLocal = do
  n <- get localCount
  set (\ s -> s {localCount = n + 1})
  return $ "v" ++ show n

getIdentLocal :: Direct.Ident -> M Local
getIdentLocal d1 = do
  x1s <- get identLocals
  case (lookup d1 x1s) of
    Just [x2] -> return x2
    _ -> unreachable "getIdentLocal"

getIdentLocals3 :: Direct.Ident -> M (Local, Local, Local)
getIdentLocals3 d1 = do
  x1s <- get identLocals
  case (lookup d1 x1s) of
    Just [x2, x3, x4] -> return (x2, x3, x4)
    _ -> unreachable "getIdentLocals3"

setIdentLocal :: Direct.Ident -> Local -> M ()
setIdentLocal d1 x1 =
  set (\ s -> s {identLocals = (d1, [x1]) : identLocals s})

setIdentLocals3 :: Direct.Ident -> (Local, Local, Local) -> M ()
setIdentLocals3 d1 (x1, x2, x3) =
  set (\ s -> s {identLocals = (d1, [x1, x2, x3]) : identLocals s})

setIdentType :: Direct.Ident -> Direct.Type -> M ()
setIdentType d1 ty1 =
  set (\ s -> s {identTypes = (d1, ty1) : identTypes s})

getIdentType :: Direct.Ident -> M Direct.Type
getIdentType d1 = do
  x1s <- get identTypes
  return $ fromMaybe (unreachable "getIdentType") (lookup d1 x1s)

putFrontier :: M ()
putFrontier = do
  d1 <- getFrontier
  put $ "s->frontier = " ++ d1 ++ ";"

getFrontier :: M String
getFrontier = do
  get frontierLocal

setFrontier :: String -> M ()
setFrontier x1 =
  set (\ s -> s {frontierLocal = x1})

generateTerm :: Direct.Term -> M ()
generateTerm t =
  case t of
    Direct.CallTerm d1 d2s -> do
      put $ "s->function = f" ++ show d1 ++ ";"
      ty1s <- mapM getIdentType d2s
      _ <- putStores "s->arguments" 0 d2s ty1s
      putFrontier
      put $ "return 1;" -- 1 tells the runtime to perform a call
    Direct.CaseTerm d1 x1s -> do
      x2 <- getIdentLocal d1
      ty1 <- getIdentType d1
      x3 <- get frontierLocal
      put $ "switch (v" ++ x2 ++ ")) {"
      forM_ (zip [0..] x1s) (generateRule x3)
      put $ "}"
    Direct.ConcatenateTerm d1 d2 (d3, t1) -> do
      todo "generateTerm ConcatenateTerm"
    Direct.UnreachableTerm ty1 () -> do
      putFrontier
      put "return 0;"
    _ -> todo "generateTerm"

generateRule :: Local -> (Int, ([Direct.Ident], Direct.Term)) -> M ()
generateRule x1 (i1, (d1s, t1)) = do
  set (\ s -> s {frontierLocal = x1})
  reallyGenerateRule i1 d1s t1

reallyGenerateRule :: Int -> [Direct.Ident] -> Direct.Term -> M ()
reallyGenerateRule i1 d1s t1 = do
  put $ "case " ++ show i1 ++ ":"
  indent $
    generateTerm t1
  -- No need for break because every term returns.



{-
    Direct.ConcatenateTerm d1 d2 (d3, t1) -> do
      -- String concatenation should not create a new data structure if one of
      -- the strings is empty.
      --
      (x1, x2, x3) <- getStringLocals d1
      (x4, x5, x6) <- getStringLocals d2
      x7 <- newLocal
      put $ "uint64_t " ++ x7 ++ ";"
      x8 <- newLocal
      put $ "uint64_t " ++ x8 ++ ";"
      x9 <- newLocal
      put $ "uint64_t " ++ x9 ++ ";"
      put $ "if (" ++ x2 ++ " = 0) {"
      indent $ do
        put $ x7 ++ " = " ++ x4 ++ ";"
        put $ x8 ++ " = " ++ x5  ++ ";"
        put $ x9 ++ " = " ++ x6 ++ ";"
      put $ "} else if (" ++ x3 ++ " = 0) {"
      indent $ do
        put $ x7 ++ " = " ++ x1 ++ ";"
        put $ x8 ++ " = " ++ x2  ++ ";"
        put $ x9 ++ " = " ++ x3 ++ ";"
      put $ "} else {"
      indent $ do
        put $ x7 ++ " = " ++ x1 ++ ";"
        put $ x8 ++ " = " ++ x2  ++ ";"
        put $ x9 ++ " = " ++ x3 ++ ";"
        -- Initialize the locals.
        x10 <- getFrontier
        put $ x7 ++ " = " ++ x10 ++ ";"
        put $ x8 ++ " = " ++ x7 ++ " + 8;"
        put $ x9 ++ " = " ++ x3 ++ " + " ++ x6 ++ ";"
        put $ "for (uint64_t i = 0; i < " ++ x3 ++ "; i++)"
        indent $
          put $ "*(uint8_t *)(" ++ x8 ++ " + i) = *(uint8_t *)(" ++ x2 ++ " + i)";
        put $ "uint64_t p = " ++ x8 ++ " + " ++ x3 ++ ";"
        put $ "for (uint64_t i = 0; i < " ++ x3 ++ "; i++)"
        indent $
          put $ "*(uint8_t *)(p + i) = *(uint8_t *)(" ++ x2 ++ " + i)";
        x11 <- newLocal
        put $ "uint64_t " ++ x11 ++ " = " ++ x10 ++ " + " ++ x2 ++ " + " ++ x5 ++ ";"
        setFrontier x11
        incAllocationCount 0 -- todo
      put $ "}"
      -- Assign the type and everything.
      setIdentLocals d3 [x7, x8, x9]
      setIdentType d3 Direct.StringType
      --
      generateTerm t1
    Direct.ConstructorTerm tyd i1 d1s (d2, t1) -> do
      -- This is the pointer to the constructor.
      x1 <- getFrontier
      ty1s <- mapM getType d1s
      put $ "*(uint64_t)" ++ x1 ++ " = " ++ show i1 ++ ";"
      offset <- putStores x1 8 d1s ty1s
      -- This is the new frontier.
      x2 <- newLocal
      put $ "uint64_t " ++ x2 ++ " = " ++ offsetString x1 (8 + offset) ++ ";"
      setFrontier x2
      incAllocationCount (8 + offset)
      -- Assign the type and everything.
      setIdentLocals d2 [x1]
      setIdentType d2 (Direct.SumType tyd)
      generateTerm t1
    Direct.StringTerm s1 (d1, t1) -> do
      -- Initialize the locals.
      x1 <- getFrontier
      put $ "*(uint64_t *)" ++ x1 ++ " = " ++ show (length s1) ++ ";"
      x2 <- newLocal
      put $ "uint64_t " ++ x2 ++ " = " ++ x1 ++ " + 8;"
      x3 <- newLocal
      put $ "uint64_t " ++ x3 ++ " = " ++ show (length s1) ++ ";"
      put $ "for (uint64_t i = 0; i < " ++ show (length s1) ++ "; i++)"
      indent $ put $ "*(uint64_t *)(" ++ x2 ++ " + i) = " ++ show s1 ++ "[i];"
      -- Update the frontier.
      let offset = align 8 (8 + length s1)
      x4 <- newLocal
      put $ "uint64_t " ++ x4 ++ " = " ++ x1 ++ " + " ++ show offset ++ ";"
      setFrontier x4
      incAllocationCount offset
      -- Assign the type and everything.
      setIdentLocals d1 [x1, x2, x3]
      setIdentType d1 Direct.StringType
      --
      generateTerm t1
    Direct.TupleTerm x1s (x2, x3) -> do
      -- This is the pointer to the tuple.
      x4 <- getFrontier
      x5s <- mapM getType x1s
      x6 <- putStores x4 0 x1s x5s
      -- This is the new frontier.
      x7 <- newLocal
      put $ "uint64_t " ++ x7 ++ " = " ++ offsetString x4 x6 ++ ";"
      setFrontier x7
      incAllocationCount x6
      -- Assign the type and everything.
      setIdentLocals x2 [x4]
      setIdentType x2 (Direct.TupleType x5s)
      generateTerm x3
    Direct.UntupleTerm x1 (x2s, x3) -> do
      x4s <- getTupleTypes x1
      x5 <- getIdentLocal x1
      _ <- putLoads x5 0 x2s x4s
      generateTerm x3
    Direct.WriteTerm d1 (t1) -> do
      (x1, x2, x3) <- getStringLocals d1
      put $ "s->string = " ++ x1 ++ ";"
      put $ "s->stringInterior = " ++ x2 ++ ";"
      put $ "s->stringLength = " ++ x3 ++ ";"
      putFrontier
      put "return 4;"

getStringLocals :: Direct.Ident -> M (Local, Local, Local)
getStringLocals = todo "getStringLocals"

align :: Int -> Int -> Int
align = todo "align"

type Local = String
type Offset = Int

getIdentLocal :: Direct.Ident -> M Local
getIdentLocal = todo "getIdentLocal"

getTupleTypes :: Direct.Ident -> M [Direct.Type]
getTupleTypes x1 = do
  x2 <- getType x1
  case x2 of
    Direct.TupleType x3s -> return x3s
    _ -> unreachable "getTupleTypes"

getIdentLocals :: Direct.Ident -> M [Local]
getIdentLocals = todo "getIdentLocals"

setIdentLocals :: Direct.Ident -> [Local] -> M ()
setIdentLocals = todo "rename"

getIdentType :: Direct.Ident -> M Direct.Type
getIdentType = todo "getIdentType"

setIdentType :: Direct.Ident -> Direct.Type -> M ()
setIdentType = todo "setType"

offsetString :: Local -> Offset -> String
offsetString s 0 = s
offsetString s n = "(" ++ s ++ " + " ++ show n ++ ")"

-- We store the maximum argument size.
setArgumentSize :: Int -> M ()
setArgumentSize = todo "setArgumentSize"






calculateOffset :: Int -> [(Direct.Ident, Direct.Type)] -> [(Direct.Ident, Direct.Type, Int)]
calculateOffset n [] = []
calculateOffset n ((d, ty) : xs) = (d, ty, n) : calculateOffset (n + typeSize ty) xs

typeSize :: Direct.Type -> Int
typeSize ty =
  case ty of
    Direct.StringType -> 3
    Direct.TupleType _ -> 1
    Direct.SumType _ -> 1

putFrontier :: M ()
putFrontier = do
  x9 <- getFrontier
  put $ "s->frontier = " ++ x9 ++ ";"



lookupIdent :: Direct.Ident -> M Local
lookupIdent = todo "lookupIdent"

lookupIdent3 :: Direct.Ident -> M (Local, Local, Local)
lookupIdent3 = todo "lookupIdent3"

loadLocal :: M Local
loadLocal = todo "loadLocal"

bind :: Direct.Ident -> String -> M a -> M a
bind _ _ _ = todo "bind"

newLocal :: M String
newLocal = todo "newLocal"

incAllocationCount :: Int -> M ()
incAllocationCount n = todo "intAllocationCount"

temp :: String -> M String
temp = todo "temp"

indent :: M a -> M a
indent m = do
  n <- getIndent
  withIndent (n + 2) m

withIndent :: Int -> M a -> M a
withIndent n m = todo "withIndent"

getIndent :: M Int
getIndent = todo "getIndent"

getType :: Direct.Ident -> M Direct.Type
getType = todo "getType"

put :: String -> M ()
put s2 = do
  n <- getIndent
  let s1 = take n (repeat ' ')
  todo "put"

setAllocationCount :: Int -> M ()
setAllocationCount n = todo "setAllocationCount"

withResetString :: M () -> M String
withResetString m = todo "withResetString"

getAllocationCount :: M Int
getAllocationCount = todo "getAllocationCount"

getLocals :: M [(Int, String)]
getLocals = todo "getLocals"

setLocals :: [(Int, String)] -> M ()
setLocals = todo "setLocals"


indexes :: [Int]
indexes = [0..]

getString :: M String
getString = todo "getString"

setString :: String -> M ()
setString s = todo "setString"



-}

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: Generator." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Generator." ++ s
