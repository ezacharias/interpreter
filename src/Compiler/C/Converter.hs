module Compiler.C.Converter where

import           Control.Monad   (forM_)
import           System.IO       (Handle, hPutStrLn)

import           Compiler.Direct

convert :: Handle -> Program -> IO ()
convert h p = run h p $ do
  putStateStruct
  putPrototypes (length (programFuns p))
  putMain
  -- _ <- todo "convert"
  return ()

run :: Handle -> Program -> M () -> IO ()
run h p m = runM m s (\ () -> return ())
  where s = S { handle = h
              , indentation = 0
              }

putStateStruct :: M ()
putStateStruct = do
  put $ "struct state {"
  indent $ do
    put $ "uintptr_t frontier;"
    put $ "uintptr_t limit;"
    put $ "void (struct state *)f;"
    put $ "uintptr_t arguments[16]"
  put $ "};"

putPrototypes :: Int -> M ()
putPrototypes i = do
  put $ "extern int main();"
  put $ "static int finished(struct state *);"
  put $ "static int unreachable(struct state *);"
  forM_ (take i [0..]) $ \ (i :: Int) -> do
    put $ "static void f" ++ show i ++ "(struct state *);"

putMain :: M ()
putMain = do
  put "extern void main() {"
  indent $ do
    put $ "struct state *s = (struct state *)malloc(sizeof(struct state));"
    put "s->frontier = (uintptr_t)malloc(512 * 1024);"
    put "s->limit = frontier + 512 * 1024;"
    put "s->f = f0;"
    put "for (;;) {"
    indent $ do
      put "s->f(s);"
    put "}"
    put "return EXIT_SUCCESS;"
  put "}"

genFinished :: M ()
genFinished = do
  put "static void finished(struct state *s) {"
  indent $ do
    put "exit(EXIT_SUCCESS);"
    put "return;"
  put "}"

genUnreachable :: M ()
genUnreachable = do
  put "static void unreachable(struct state *s) {"
  indent $ do
    put "err(EXIT_FAILURE, \"unreachable\");"
    put "return;"
  put "}"

genGC :: M ()
genGC = do
  put "static void gc(struct state *s) {"
  indent $ do
    put "err(EXIT_FAILURE, \"out of memory\");"
    put "return;"
  put "}"

genFun :: (Ident, Fun) -> M ()
genFun (d, Fun ds tys t) = do
  s <- getFunName d
  n <- allocationAmount t
  put $ "static void " ++ s ++ "(struct state *s) {"
  indent $ do
    put $ "uintptr_t frontier = s->frontier;"
    put $ "if (frontier + " ++ show n ++ " > s->limit) {"
    indent $ do
      put $ "s->gc;"
      put "return;"
    put $ "}"
    -- Load the arguments.
    _ <- todo "load arguments"
    putTerm t
  put $ "}"
  return ()

putTerm :: Term -> M ()
putTerm t =
  case t of
    CallTerm d1 d2s -> do
      s1 <- getFunIdent d1
      put $ "s->frontier = frontier;"
      put $ "s->f = " ++ s1 ++ ";"
      -- Store arguments.
      _ <- todo "call"
      put "return;"
    CaseTerm d1 c1s -> do
      s1 <- getIdent d1
      put $ "switch (*(uintptr_t *)" ++ s1 ++ ") {"
      indent $ do
        mapM_ (uncurry (putRule s1)) (zip [0..] c1s)
      put $ "}"
    ConcatenateTerm d1 d2 d3 t1 -> do
      s1 <- gen
      s2 <- getIdent d2
      s3 <- getIdent d3
      _ <- todo "concatenate"
      return ()
    ConstructorTerm d1 _ i d2s t1 -> do
      s1 <- gen
      s2s <- mapM getIdent d2s
      put $ "uintptr_t " ++ s1 ++ " = heap;"
      put $ "*(uintptr_t)" ++ s1 ++ " = " ++ show i ++ ";"
      forM_ (zip s2s [1..]) $ \ (s2, i :: Int) -> do
        put $ "*(uintptr_t)(" ++ s1 ++ " + " ++ show i ++ " * (uintptr_t)) = " ++ s2 ++ ";"
      bind d1 s1 $ do
        putTerm t1
    ExitTerm -> do
      put "s->frontier = frontier;"
      put "s->f = finished;"
      put "return;"
    StringTerm d1 x2 t1 -> do
      s1 <- gen
      i <- return $ length x2
      put $ "uintptr_t " ++ s1 ++ " = heap;"
      put $ "*(uintptr_t *)" ++ s1 ++ " = 0;"
      put $ "*(uintptr_t *)(" ++ s1 ++ " + sizeof(uintptr_t)) = " ++ show i ++ ";"
      s2 <- gen
      put $ "char *" ++ s2 ++ " = " ++ show x2 ++ ";"
      put $ "for (i = 0; i++; i < " ++ show i ++ ") {"
      indent $ do
        put $ "*(char *)(" ++ s1 ++ " + 2 * sizeof(uintptr_t) + i * sizeof(char)) = *(char *)(" ++ s2 ++ " + i * sizeof(char));"
      put $ "}"
      bind d1 s1 $ do
        putTerm t1
    TupleTerm d1 d2s t1 -> do
      s1 <- gen
      put $ "uintptr " ++ s1 ++ " = heap;"
      put $ "(uintptr_t *)heap = 0";
      put $ "heap += sizeof(uintptr_t);"
      forM_ d2s $ \ d2 -> do
        s2 <- getIdent d2
        put $ "(uintptr_t *)heap = " ++ s2 ++ ";"
        put $ "heap += sizeof(uintptr_t);"
      ty2s <- mapM getType d2s
      bind d1 s1 $ do
        putTerm t1
    UnreachableTerm -> do
      put "s->frontier = frontier;"
      put "s->unreachable"
      put "return;"
    UntupleTerm d1s d2 t1 -> do
      s1s <- mapM (const gen) d1s
      s2 <- getIdent d2
      TupleType ty1s <- getType d2
      forM_ (zip3 d1s s1s [1..]) $ \ (d1, s1, i :: Int) -> do
        put $ s1 ++ " = *(uintptr_t *)(" ++ s2 ++ " + " ++ show i ++ " * sizeof(uintptr_t *));"
      binds d1s s1s $ do
        putTerm t1
    WriteTerm d1 t1 -> do
      put "printf(\"Write\\n\");"
      putTerm t1

putRule :: String -> Int -> ([Ident], Term) -> M ()
putRule s1 i (d2s, t1) = do
  s2s <- mapM (const gen) d2s
  put $ "case " ++ show i ++ ": {"
  indent $ do
    forM_ (zip s2s [1..]) $ \ (s2, i :: Int) -> do
      put $ "uintptr_t " ++ s2 ++ " = *(uintptr_t *)(" ++ s1 ++ " + " ++ show i ++ " * sizeof(uintptr_t));"
    binds d2s s2s $ do
      putTerm t1

getIdent :: Ident -> M String
getIdent = todo "getIdent"

getType :: Ident -> M Type
getType = todo "getType"

bind :: Ident -> String -> M () -> M ()
bind = todo "bind"

binds :: [Ident] -> [String] -> M () -> M ()
binds = todo "binds"

gen :: M String
gen = todo "gen"

getFunIdent :: Ident -> M String
getFunIdent = todo "getFunIdent"

allocationAmount :: Term -> M Int
allocationAmount = todo "allocationAmount"

getFunName :: Ident -> M String
getFunName = todo "getFunName"

put :: String -> M ()
put s = do
  h <- getHandle
  i <- getIndentation
  liftIO $ hPutStrLn h ((replicate i ' ') ++ s)

indent :: M () -> M ()
indent m = M $ \ s k -> runM m (s {indentation = indentation s + 2}) k

newtype M a = M {runM :: State -> (a -> IO ()) -> IO ()}

instance Monad M where
  return x = M $ \ s k -> k x
  m >>= f = M $ \ s k -> runM m s (\ x -> runM (f x) s k)

data State = S
  { handle      :: Handle
  , indentation :: Int
  }

liftIO :: IO a -> M a
liftIO m = M $ \ h k -> m >>= k

getHandle :: M Handle
getHandle = M $ \ s k -> k (handle s)

getIndentation :: M Int
getIndentation = M $ \ s k -> k (indentation s)

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: C.Converter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: C.Converter." ++ s
