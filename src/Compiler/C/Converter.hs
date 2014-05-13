-- We assume 64 bit pointers.

module Compiler.C.Converter where

import           Control.Monad   (forM_)
import           Data.Maybe      (fromMaybe)
import           System.IO       (Handle, hPutStrLn)

import           Compiler.Direct

convert :: Handle -> Program -> IO ()
convert h p = run h p $ do
  putIncludes
  putPrototypes (length (programFuns p))
  putMain (programStart p)
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
  put $ "#include \"header.h\""

putPrototypes :: Int -> M ()
putPrototypes i = do
  put $ "extern int main();"
  forM_ (take i [0..]) $ \ (i :: Int) -> do
    put $ "static void f" ++ show i ++ "(struct state *);"

-- d is the ident of the start function
putMain :: Ident -> M ()
putMain d = do
  s <- getFunName d
  put "extern int main() {"
  indent $ do
    put $ "struct state *s = (struct state *)malloc(sizeof(struct state));"
    put $ "s->sentinel = 1;"
    put $ "s->frontier = (uint64_t)malloc(HEAP_SIZE);"
    put $ "s->limit = s->frontier + HEAP_SIZE;"
    put $ "s->f = " ++ s ++ ";"
    put $ "for (;;) {"
    indent $ do
      put $ "s->f(s);"
    put $ "}"
    put $ "return EXIT_SUCCESS;"
  put $ "}"

putFun :: (Ident, Fun) -> M ()
putFun (d, Fun ds tys t) = do
  if (length ds == length tys) then return () else error "length"
  resetLocals
  s <- getFunName d
  n <- return $ allocationAmount t
  ss <- mapM (const gen) ds
  put $ "static void " ++ s ++ "(struct state *s) {"
  indent $ do
    -- put $ "printf(\"" ++ s ++ " start\\n\");"
    put $ "uint64_t frontier = s->frontier;"
    put $ "if (frontier + " ++ show n ++ " >= s->limit) {"
    indent $ do
      put $ "printf(\"gc: " ++ s ++ " " ++ show (length ds) ++ "\\n\");"
      put $ "s->f = gc;"
      put $ "s->saved = " ++ s ++ ";"
      put $ "s->argument_bitfield = " ++ bitfield tys ++ ";"
      put "return;"
    put $ "}"
    forM_ (zip ss [0..]) $ \ (s, i :: Int) -> do
      put $ "uint64_t " ++ s ++ " = s->arguments[" ++ show i ++ "];"
      put $ "check_one(s, " ++ s ++ ");"
    binds ds ss $ do
      putTerm t
  put $ "}"

allocationAmount :: Term -> Int
allocationAmount t =
  case t of
    CallTerm _ _ -> 0
    CaseTerm _ rs -> foldl1 max (map allocationAmount (map snd rs))
    -- Maximum string length is 32.
    ConcatenateTerm _ _ _ t -> 8 + 8 + 8 + 40
    ConstructorTerm _ _ _ ds t -> align (8 + 8 + length ds * 8) + allocationAmount t
    ExitTerm -> 0
    -- Maximum string length is 32.
    StringTerm _ x t -> align (8 + 8 + 8 + length x) + allocationAmount t
    TupleTerm _ ds t -> align (8 + 8 + length ds * 8) + allocationAmount t
    UnreachableTerm -> 0
    UntupleTerm _ _ t -> allocationAmount t
    WriteTerm _ t -> allocationAmount t

align :: Int -> Int
align n = ((n + 16 - 1) `div` 16) * 16

bitfield :: [Type] -> String
bitfield tys = show (bitfield' tys)

bitfield' :: [Type] -> Integer
bitfield' [] = 1
bitfield' (ty:tys) =
  case ty of
    StringType -> 1 + 2 * bitfield' tys
    TupleType _ -> 1 + 2 * bitfield' tys
    SumType _ -> 1 + 2 * bitfield' tys

putTerm :: Term -> M ()
putTerm t =
  case t of
    CallTerm d1 d2s -> do
      s1 <- getFunName d1
      put $ "s->frontier = frontier;"
      put $ "s->f = " ++ s1 ++ ";"
      s2s <- mapM getIdent d2s
      forM_ (zip [0..] s2s) $ \ (i :: Int, s2) -> do
        put $ "assert(" ++ s2 ++ " != 0);"
        put $ "s->arguments[" ++ show i ++ "] = " ++ s2 ++ ";"
      put "return;"
    CaseTerm d1 c1s -> do
      s1 <- getIdent d1
      put $ "switch (*(uint16_t *)(" ++ s1 ++ " + 2)) {"
      indent $ do
        mapM_ (uncurry (putRule s1)) (zip [0..] c1s)
        put "default: {"
        indent $ do
          put $ "errx(EXIT_FAILURE, \"bad constructor\");"
        put $ "}"
      put $ "}"
    ConcatenateTerm d1 d2 d3 t1 -> do
      _ <- todo "concat"
      s1 <- gen
      s2 <- getIdent d2
      s3 <- getIdent d3
      s4 <- gen
      s5 <- gen
      s6 <- gen
      put $ "uint64_t " ++ s4 ++ " = *(uint64_t *)(" ++ s2 ++ " + sizeof(uint64_t));"
      put $ "uint64_t " ++ s5 ++ " = *(uint64_t *)(" ++ s3 ++ " + sizeof(uint64_t));"
      put $ "uint64_t " ++ s6 ++ " = " ++ s4 ++ " + " ++ s5 ++ ";"
      put $ "uint64_t " ++ s1 ++ ";"
      put $ "if (" ++ s4 ++ " == 0) {"
      indent $ do
        put $ s1 ++ " = " ++ s5 ++ ";"
      put $ "} else if (" ++ s5 ++ " == 0) {"
      indent $ do
        put $ s1 ++ " = " ++ s4 ++ ";"
      put $ "} else if (" ++ s6 ++ " > 32) {"
      indent $ do
        put $ "errx(EXIT_FAILURE, \"concatenation longer than 32\");"
      put $ "} else {"
      indent $ do
        put $ s1 ++ " = frontier;"
        put $ "frontier += sizeof(uintptr) + sizeof(uintptr) + ((" ++ s6 ++ " + sizeof(uint64_t) - 1) / sizeof(uint64_t)) * sizeof(uint64_t);"
        put $ "*" ++ s1 ++ " = 0;"
        put $ "*(" ++ s1 ++ " + sizeof(uint64_t)) = " ++ s6 ++ ";"
        put $ "for (uint64_t i = 0; i < " ++ s4 ++ "; i++) {"
        indent $ do
          put $ "*(uint8_t *)(" ++ s1 ++ " + sizeof(uint64_t) + sizeof(uint64_t) + i) = *(uint8_t)(" ++ s2 ++ " + sizeof(uint64_t) + sizeof(uint64_t) + i);"
        put $ "}"
        put $ "for (uint64_t i = 0; i < " ++ s5 ++ "; i++) {"
        indent $ do
          put $ "*(uint8_t *)(" ++ s1 ++ " + sizeof(uint64_t) + sizeof(uint64_t) + " ++ s4 ++ " + i) = *(uint8_t)(" ++ s3 ++ " + sizeof(uint64_t) + sizeof(uint64_t) + i);"
        put $ "}"
      put $ "}"
      bind d1 s2 $ do
        putTerm t1
    ConstructorTerm d1 _ i d2s t1 -> do
      s1 <- gen
      s2s <- mapM getIdent d2s
      put $ "uint64_t " ++ s1 ++ " = frontier;"
      put $ "frontier += " ++ show (align (8 + 8 + length d2s * 8)) ++ ";"
      put $ "*(uint8_t *)" ++ s1 ++ " = 1;"
      put $ "*(uint8_t *)(" ++ s1 ++ " + 1) = 0;"
      put $ "*(uint16_t *)(" ++ s1 ++ " + 2) = " ++ show i ++ ";"
      put $ "*(uint32_t *)(" ++ s1 ++ " + 4) = " ++ bitfield (map (const StringType) d2s) ++ ";"
      put $ "*(uint64_t *)(" ++ s1 ++ " + 8) = 0;"
      forM_ (zip s2s [0..]) $ \ (s2, i :: Int) -> do
        put $ "*(uint64_t *)(" ++ s1 ++ " + " ++ show (8 + 8 + i * 8) ++ ") = " ++ s2 ++ ";"
      put $ "check_one(s, " ++ s1 ++ ");"
      bind d1 s1 $ do
        putTerm t1
    ExitTerm -> do
      put "s->frontier = frontier;"
      put "s->f = finished;"
      put "return;"
    StringTerm d1 x2 t1 -> do
      s1 <- gen
      i <- return $ length x2
      put $ "uint64_t " ++ s1 ++ " = frontier;"
      put $ "frontier += " ++ show (align (8 + 8 + 8 + length x2)) ++ ";"
      put $ "*(uint64_t *)" ++ s1 ++ " = 0;"
      put $ "*(uint8_t *)" ++ s1 ++ " = 2;"
      put $ "*(uint64_t *)(" ++ s1 ++ " + 8) = 0;"
      put $ "*(uint64_t *)(" ++ s1 ++ " + 16) = " ++ show i ++ ";"
      s2 <- gen
      put $ "uint64_t " ++ s2 ++ " = (uint64_t)" ++ show x2 ++ ";"
      put $ "for (uint64_t i = 0; i < " ++ show i ++ "; i++) {"
      indent $ do
        put $ "*(char *)(" ++ s1 ++ " + 24 + i) = *(char *)(" ++ s2 ++ " + i);"
      put $ "}"
      bind d1 s1 $ do
        putTerm t1
    TupleTerm d1 d2s t1 -> do
      s1 <- gen
      s2s <- mapM getIdent d2s
      put $ "uint64_t " ++ s1 ++ " = frontier;"
      put $ "frontier += " ++ show (align (8 + 8 + length d2s * 8)) ++ ";"
      put $ "*(uint8_t *)" ++ s1 ++ " = 0;"
      put $ "*(uint8_t *)(" ++ s1 ++ " + 1) = 0;"
      put $ "*(uint16_t *)(" ++ s1 ++ " + 2) = 0;"
      put $ "*(uint32_t *)(" ++ s1 ++ " + 4) = " ++ bitfield (map (const StringType) d2s) ++ ";"
      put $ "*(uint64_t *)(" ++ s1 ++ " + 8) = 0;"
      forM_ (zip [0..] s2s) $ \ (i :: Int, s2) -> do
        put $ "*(uint64_t *)(" ++ s1 ++ " + " ++ show (8 + 8 + i * 8) ++ ") = " ++ s2 ++ ";"
      put $ "check_one(s, " ++ s1 ++ ");"
      bind d1 s1 $ do
        putTerm t1
    UnreachableTerm -> do
      put "s->frontier = frontier;"
      put "s->f = unreachable;"
      put "return;"
    UntupleTerm d1s d2 t1 -> do
      s1s <- mapM (const gen) d1s
      s2 <- getIdent d2
      forM_ (zip s1s [0..]) $ \ (s1, i :: Int) -> do
        put $ "uint64_t " ++ s1 ++ " = *(uint64_t *)(" ++ s2 ++ " + " ++ show (8 + 8 + i * 8) ++ ");"
        put $ "check_one(s, " ++ s1 ++ ");"
      binds d1s s1s $ do
        putTerm t1
    WriteTerm d1 t1 -> do
      s1 <- getIdent d1
      s2 <- gen
      put $ "uint64_t " ++ s2 ++ " = *(uint64_t *)(" ++ s1 ++ " + 16);"
      put $ "write(1, (uint8_t *)(" ++ s1 ++ " + 24), (size_t)" ++ s2 ++ ");"
      put $ "write(1, \"\\n\", 1);"
      putTerm t1

putRule :: String -> Int -> ([Ident], Term) -> M ()
putRule s1 i (d2s, t1) = do
  s2s <- mapM (const gen) d2s
  put $ "case " ++ show i ++ ": {"
  indent $ do
    forM_ (zip s2s [0..]) $ \ (s2, i :: Int) -> do
      put $ "uint64_t " ++ s2 ++ " = *(uint64_t *)(" ++ s1 ++ " + " ++ show (8 + 8 + i * 8) ++ ");"
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
