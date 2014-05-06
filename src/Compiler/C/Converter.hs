module Compiler.C.Converter where

import           Control.Monad   (forM_)
import           Data.Maybe      (fromMaybe)
import           System.IO       (Handle, hPutStrLn)

import           Compiler.Direct

convert :: Handle -> Program -> IO ()
convert h p = run h p $ do
  putIncludes
  putStateStruct
  putPrototypes (length (programFuns p))
  putMain (programStart p)
  putFinished
  putUnreachable
  putGC
  mapM_ putFun (programFuns p)

run :: Handle -> Program -> M () -> IO ()
run h p m = runM m s (\ () _ -> return ()) 0
  where s = S { handle = h
              , indentation = 0
              , funNames = zip (map fst (programFuns p)) [0..]
              , locals = []
              }

putIncludes :: M ()
putIncludes = do
  put $ "#include <stdint.h>"
  put $ "#include <stdio.h>"
  put $ "#include <stdlib.h>"

putStateStruct :: M ()
putStateStruct = do
  put $ "struct state {"
  indent $ do
    put $ "uintptr_t frontier;"
    put $ "uintptr_t limit;"
    put $ "void (*f)(struct state *);"
    put $ "uintptr_t arguments[16];"
    put $ "void (*saved)(struct state *);"
  put $ "};"

putPrototypes :: Int -> M ()
putPrototypes i = do
  put $ "extern int main();"
  put $ "static void finished(struct state *);"
  put $ "static void unreachable(struct state *);"
  put $ "static void gc(struct state *);"
  forM_ (take i [0..]) $ \ (i :: Int) -> do
    put $ "static void f" ++ show i ++ "(struct state *);"

-- d is the ident of the start function
putMain :: Ident -> M ()
putMain d = do
  s <- getFunName d
  put "extern void main() {"
  indent $ do
    put $ "struct state *s = (struct state *)malloc(sizeof(struct state));"
    put $ "s->frontier = (uintptr_t)malloc(512 * 1024);"
    put $ "s->limit = frontier + 512 * 1024;"
    put $ "s->f = " ++ s ++ ";"
    put $ "for (;;) {"
    indent $ do
      put $ "s->f(s);"
    put $ "}"
    put $ "return EXIT_SUCCESS;"
  put $ "}"

putFinished :: M ()
putFinished = do
  put $ "static void finished(struct state *s) {"
  indent $ do
    put $ "exit(EXIT_SUCCESS);"
    put $ "return;"
  put "}"

putUnreachable :: M ()
putUnreachable = do
  put $ "static void unreachable(struct state *s) {"
  indent $ do
    put $ "err(EXIT_FAILURE, \"unreachable\");"
    put $ "return;"
  put $ "}"

putGC :: M ()
putGC = do
  put $ "static void gc(struct state *s) {"
  indent $ do
    put $ "err(EXIT_FAILURE, \"out of memory\");"
    put $ "return;"
  put $ "}"

putFun :: (Ident, Fun) -> M ()
putFun (d, Fun ds tys t) = do
  resetLocals
  s <- getFunName d
  n <- return $ allocationAmount t
  ss <- mapM (const gen) ds
  put $ "static void " ++ s ++ "(struct state *s) {"
  indent $ do
    put $ "uintptr_t frontier = s->frontier;"
    put $ "if (frontier + " ++ show n ++ " > s->limit) {"
    indent $ do
      put $ "s->f = gc;"
      put $ "s->saved = " ++ s ++ ";"
      put "return;"
    put $ "}"
    forM_ (zip ss [0..]) $ \ (s, i :: Int) -> do
      put $ "uintptr_t " ++ s ++ " = *(uintptr_t *)(s->arguments + " ++ show i ++ " * sizeof(uintptr_t));"
    binds ds ss $ do
      putTerm t
  put $ "}"

allocationAmount :: Term -> Int
allocationAmount t =
  case t of
    CallTerm _ _ -> 0
    CaseTerm _ rs -> foldl1 max (map allocationAmount (map snd rs))
    ConcatenateTerm _ _ _ t -> 8 + 8 + (32)
    ConstructorTerm _ _ _ ds t -> 8 + 8 * length ds + allocationAmount t
    ExitTerm -> 0
    StringTerm _ _ t ->  8 + 32 + allocationAmount t
    TupleTerm _ ds t -> 8 + 8 * length ds + allocationAmount t
    UnreachableTerm -> 0
    UntupleTerm _ _ t -> allocationAmount t
    WriteTerm _ t -> allocationAmount t

putTerm :: Term -> M ()
putTerm t =
  case t of
    CallTerm d1 d2s -> do
      s1 <- getFunName d1
      put $ "s->frontier = frontier;"
      put $ "s->f = " ++ s1 ++ ";"
      s2s <- mapM getIdent d2s
      forM_ (zip [0..] s2s) $ \ (i :: Int, s2) -> do
        put $ "*(uintptr_t *)(s->arguments + " ++ show i ++ " * sizeof(uintptr_t)) = " ++ s2 ++ ";"
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
      put $ "uintptr_t " ++ s1 ++ " = frontier;"
      put $ "frontier += sizeof(uintptr_t) + " ++ show (length d2s) ++ " * sizeof(uintptr_t);"
      put $ "*(uintptr_t)" ++ s1 ++ " = " ++ show i ++ ";"
      forM_ (zip s2s [1..]) $ \ (s2, i :: Int) -> do
        put $ "*(uintptr_t *)(" ++ s1 ++ " + " ++ show i ++ " * sizeof(uintptr_t)) = " ++ s2 ++ ";"
      bind d1 s1 $ do
        putTerm t1
    ExitTerm -> do
      put "s->frontier = frontier;"
      put "s->f = finished;"
      put "return;"
    StringTerm d1 x2 t1 -> do
      s1 <- gen
      i <- return $ length x2
      put $ "frontier += sizeof(uintptr_t) + sizeof(uintptr_t) + (" ++ show (length x2) ++ " + sizeof(uintptr_t) - 1) % sizeof(uintptr_t) * sizeof(uintptr_t);"
      put $ "uintptr_t " ++ s1 ++ " = frontier;"
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
      put $ "uintptr " ++ s1 ++ " = frontier;"
      put $ "frontier += sizeof(uintptr_t) + " ++ show (length d2s) ++ " * sizeof(uintptr_t);"
      put $ "*(uintptr_t *)" ++ s1 ++ " = 0";
      forM_ d2s $ \ d2 -> do
        s2 <- getIdent d2
        put $ "*(uintptr_t *)frontier = " ++ s2 ++ ";"
      bind d1 s1 $ do
        putTerm t1
    UnreachableTerm -> do
      put "s->frontier = frontier;"
      put "s->unreachable"
      put "return;"
    UntupleTerm d1s d2 t1 -> do
      s1s <- mapM (const gen) d1s
      s2 <- getIdent d2
      forM_ (zip3 d1s s1s [1..]) $ \ (d1, s1, i :: Int) -> do
        put $ s1 ++ " = *(uintptr_t *)(" ++ s2 ++ " + " ++ show i ++ " * sizeof(uintptr_t));"
      binds d1s s1s $ do
        putTerm t1
    WriteTerm d1 t1 -> do
      s1 <- getIdent d1
      s2 <- gen
      put $ "uintptr_t " ++ s2 ++ " = *(uintptr_t *)(" ++ s1 ++ " + sizeof(uintptr_t));"
      put $ "write(stdout, (uint8_t *)(" ++ s1 ++ " + 2 * sizeof(uintptr_t)), (size_t)" ++ s2 ++ ");"
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
  put $ "}"

getIdent :: Ident -> M String
getIdent d = do
  xs <- look locals
  return $ fromMaybe (unreachable "getIdent") (lookup d xs)

bind :: Ident -> String -> M () -> M ()
bind d x m = M $ \ s k i -> runM m (s {locals = (d, x) : locals s}) k i

binds :: [Ident] -> [String] -> M () -> M ()
binds [] [] m = m
binds (d:ds) (s:ss) m = bind d s $ binds ds ss m
binds _ _ _ = unreachable "binds"

gen :: M String
gen =  M $ \ s k i -> k ('l' : show i) (i + 1)

resetLocals :: M ()
resetLocals =  M $ \ s k i -> k () 0

getFunName :: Ident -> M String
getFunName d = do
  xs <- look funNames
  return $ 'f' : show (fromMaybe (unreachable "getFunName") (lookup d xs))

put :: String -> M ()
put s = do
  h <- getHandle
  i <- getIndentation
  liftIO $ hPutStrLn h ((replicate i ' ') ++ s)

indent :: M () -> M ()
indent m = M $ \ s k -> runM m (s {indentation = indentation s + 2}) k

newtype M a = M {runM :: State -> (a -> Int -> IO ()) -> Int -> IO ()}

instance Monad M where
  return x = M $ \ s k -> k x
  m >>= f = M $ \ s k -> runM m s (\ x -> runM (f x) s k)

data State = S
  { handle      :: Handle
  , indentation :: Int
  , funNames    :: [(Ident, Int)]
  , locals      :: [(Ident, String)]
  }

look :: (State -> a) -> M a
look f = M $ \ s k -> k (f s)

liftIO :: IO a -> M a
liftIO m = M $ \ h k i -> m >>= \ x -> k x i

getHandle :: M Handle
getHandle = M $ \ s k -> k (handle s)

getIndentation :: M Int
getIndentation = M $ \ s k -> k (indentation s)

-- Utility Functions

todo :: String -> a
todo s = error $ "todo: C.Converter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: C.Converter." ++ s
