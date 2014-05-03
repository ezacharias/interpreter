module Compiler.Simple.Check where

import Compiler.Simple

check :: Program -> Maybe String
check p = run p $ do
  checkMain (programMain p)
  mapM_ checkFun (programFuns p)

checkMain :: Ident -> M ()
checkMain d = do
  ty <- getFunType d
  case ty of
    SumType _ -> return ()
    _ -> fail "check main type"

checkFun :: (Ident, Fun) -> M ()
checkFun (d, Fun ty1 t) = do
  ty2 <- checkTerm t
  if ty1 == ty2
    then return ()
    else fail "ty"

checkTerm :: Term -> M Type
checkTerm t =
  case t of
    ApplyTerm t1 t2 -> do
      ty1 <- checkTerm t1
      case ty1 of
        ArrowType ty2 ty3 -> do
          ty4 <- checkTerm t2
          assert (ty2 == ty4)
          return ty3
        _ ->
          fail "a1"
    BindTerm d1 t1 t2 -> do
      ty1 <- checkTerm t1
      bind d1 ty1 $
        checkTerm t2
    CaseTerm t1 cs -> do
      ty1 <- checkTerm t1
      case ty1 of
        SumType d1 -> do
          tyss <- getSum d1
          tys <- mapM checkRule (zip tyss cs)
          checkTypes tys
        _ ->
          fail "c"
    CatchTerm d1 d2 ty1 t2 -> do
      ty2 <- checkTerm t2
      assert (ty1 == ty2)
      (ty3, ty4) <- getTag d1
      tyss <- getSum d2
      case tyss of
        [[ty5, ArrowType ty6 (SumType d3)], [ty7]] -> do
          assert (ty3 == ty5)
          assert (ty4 == ty7)
          assert (d2 == d3)
          assert (ty2 == ty7)
          return $ SumType d2
        _ ->
          fail $ "a2: " ++ show tyss
    ConcatenateTerm t1 t2 -> do
      ty1 <- checkTerm t1
      ty2 <- checkTerm t2
      assert (ty1 == StringType)
      assert (ty2 == StringType)
      return StringType
    ConstructorTerm d1 i t1s -> do
      tyss <- getSum d1
      assert (i < length tyss)
      ty1 <- mapM checkTerm t1s
      ty2 <- return $ tyss !! i
      assert (ty1 == ty2)
      return $ SumType d1
    FunTerm d ->
      getFunType d
    LambdaTerm d1 ty1 t1 -> do
      ty2 <- bind d1 ty1 $
               checkTerm t1
      return $ ArrowType ty1 ty2
    StringTerm s ->
      return StringType
    ThrowTerm d1 t1 -> do
      ty1 <- checkTerm t1
      (ty2, ty3) <- getTag d1
      assert (ty1 == ty2)
      return ty3
    TupleTerm t1s -> do
      ty1s <- mapM checkTerm t1s
      return $ TupleType ty1s
    UnitTerm ->
      return UnitType
    UnreachableTerm ty ->
      return ty
    UntupleTerm d1s t1 t2 -> do
      ty1 <- checkTerm t1
      case ty1 of
        TupleType ty1s -> do
          binds d1s ty1s $ do
            checkTerm t2
        _ ->
          fail "b"
    VariableTerm d1 ->
      getIdent d1

checkTypes :: [Type] -> M Type
checkTypes [] = fail "a3"
checkTypes [ty1] = return ty1
checkTypes (ty1:ty2:tys) | ty1 == ty2 = checkTypes (ty2:tys)
checkTypes (ty1:ty2:tys) | otherwise  = fail "a4"

checkRule :: ([Type], ([Ident], Term)) -> M Type
checkRule (tys, (ds, t)) = binds ds tys $ checkTerm t

assert :: Bool -> M ()
assert True = return ()
assert False = fail "a5"

binds :: [Ident] -> [Type] -> M a -> M a
binds [] [] m = m
binds (d:ds) (ty:tys) m = bind d ty $ binds ds tys m
binds _ _ m = fail "a6"

newtype M a = M { runM :: (a -> Maybe String) -> Program -> [(Ident, Type)] -> Maybe String }

instance Monad M where
  return x = M $ \ k p r -> k x
  m >>= f = M $ \ k p r -> runM m (\ x -> runM (f x) k p r) p r
  fail s = M $ \ k p r -> Just s

run :: Program -> M () -> Maybe String
run p m = runM m (const Nothing) p []

getProgram :: M Program
getProgram = M $ \ k p r -> k p

getFunType :: Ident -> M Type
getFunType d = do
  p <- getProgram
  Fun ty _ <- maybe (fail "a8") return (lookup d (programFuns p))
  return ty

getSum :: Ident -> M [[Type]]
getSum d = do
  p <- getProgram
  Sum tyss <- maybe (fail "a9") return (lookup d (programSums p))
  return tyss

getTag :: Ident -> M (Type, Type)
getTag d = do
  p <- getProgram
  Tag ty1 ty2 <- maybe (fail "a7") return (lookup d (programTags p))
  return (ty1, ty2)

bind :: Ident -> Type -> M a -> M a
bind d ty m = M $ \ k p r -> runM m k p ((d,ty):r)

getEnv :: M [(Ident, Type)]
getEnv = M $ \ k p r -> k r

getIdent :: Ident -> M Type
getIdent d = do
  r <- getEnv
  maybe (fail "a10") return (lookup d r)
