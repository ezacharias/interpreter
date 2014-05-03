module Compiler.CPS.Check where

-- import Debug.Trace (trace)
import Compiler.CPS

check :: Program -> Maybe String
check p = run p $ do
  checkStart (programStart p)
  mapM_ checkFun (programFuns p)

checkStart :: Ident -> M ()
checkStart d = do
  tys <- getFunType d
  case tys of
    [] -> return ()
    _ -> fail "check start type"

checkFun :: (Ident, Fun) -> M ()
checkFun (_, Fun d1s ty1s t) = do
  assert (length d1s == length ty1s) "checkFun"
  binds d1s ty1s $
    checkTerm t

checkTerm :: Term -> M ()
checkTerm t =
  case t of
    ApplyTerm d1 d2s -> do
      ty1 <- getIdent d1
      case ty1 of
        ArrowType ty1s -> do
          ty2s <- mapM getIdent d2s
          assert (ty1s == ty2s) $ "arr:\n" ++ show ty1s ++ "\n" ++ show ty2s
        _ -> fail "a"
    BindTerm d1 d2 t1 -> do
      ty2 <- getIdent d2
      bind d1 ty2 $
        checkTerm t1
    CallTerm d1 d2s -> do
      ty1s <- getFunType d1
      ty2s <- mapM getIdent d2s
      assert (ty1s == ty2s) "call"
    CaseTerm d1 cs -> do
      ty1 <- getIdent d1
      case ty1 of
        SumType d1 -> do
          tyss <- getSum d1
          mapM_ checkRule (zip tyss cs)
        _ ->
          fail "c"
    ConcatenateTerm d1 d2 d3 t1 -> do
      ty2 <- getIdent d2
      ty3 <- getIdent d3
      assert (ty2 == StringType) "cat1"
      assert (ty3 == StringType) "cat2"
      bind d1 StringType $
        checkTerm t1
    ConstructorTerm d0 d1 i d2s t1 -> do
      tyss <- getSum d1
      assert (i < length tyss) "cons1"
      ty2s <- mapM getIdent d2s
      ty3s <- return $ tyss !! i
      assert (ty2s == ty3s) $ "cons2: " ++ show i ++ " -- \n" ++ show tyss ++ " -- \n" ++ show ty2s -- ++ show ty2s ++ " " ++ show ty3s
      bind d0 (SumType d1) $
        checkTerm t1
    ExitTerm ->
      return ()
    LambdaTerm d0 d1s ty1s t1 t2 -> do
      assert (length d1s == length ty1s) "lambda binds"
      binds d1s ty1s $
        checkTerm t1
      bind d0 (ArrowType ty1s) $
        checkTerm t2
    StringTerm d0 s t1 ->
      bind d0 StringType $
        checkTerm t1
    TupleTerm d0 d1s t1 -> do
      ty1s <- mapM getIdent d1s
      bind d0 (TupleType ty1s) $
        checkTerm t1
    UnreachableTerm ->
      return ()
    UntupleTerm d0s d1 t1 -> do
      ty1 <- getIdent d1
      case ty1 of
        TupleType ty1s -> do
          assert (length d0s == length ty1s) "untuple binds"
          binds d0s ty1s $ do
            checkTerm t1
        _ ->
          fail "b"
    WriteTerm s t ->
      checkTerm t

checkRule :: ([Type], ([Ident], Term)) -> M ()
checkRule (tys, (ds, t)) = do
  assert (length ds == length tys) ("rule binds: " ++ show (length ds) ++ " " ++ show tys)
  binds ds tys $ checkTerm t

assert :: Bool -> String -> M ()
assert True _ = return ()
assert False s = fail s

binds :: [Ident] -> [Type] -> M a -> M a
binds [] [] m = m
binds (d:ds) (ty:tys) m = bind d ty $ binds ds tys m
binds _ _ m = fail "binds"

newtype M a = M { runM :: (a -> Maybe String) -> Program -> [(Ident, Type)] -> Maybe String }

instance Monad M where
  return x = M $ \ k p r -> k x
  m >>= f = M $ \ k p r -> runM m (\ x -> runM (f x) k p r) p r
  fail s = M $ \ k p r -> Just s

run :: Program -> M () -> Maybe String
run p m = runM m (const Nothing) p []

getProgram :: M Program
getProgram = M $ \ k p r -> k p

getFunType :: Ident -> M [Type]
getFunType d = do
  p <- getProgram
  Fun _ tys _ <- maybe (fail "a8") return (lookup d (programFuns p))
  return tys

getSum :: Ident -> M [[Type]]
getSum d = do
  p <- getProgram
  Sum tyss <- maybe (fail $ "getSum: " ++ show d) return (lookup d (programSums p))
  return tyss

bind :: Ident -> Type -> M a -> M a
bind d ty m = M $ \ k p r -> runM m k p ((d,ty):r)

getEnv :: M [(Ident, Type)]
getEnv = M $ \ k p r -> k r

getIdent :: Ident -> M Type
getIdent d = do
  r <- getEnv
  maybe (fail "a10") return (lookup d r)
