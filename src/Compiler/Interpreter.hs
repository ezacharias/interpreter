module Compiler.Interpreter where

import           Data.IntMap     (IntMap)
import qualified Data.IntMap     as IntMap
import           Data.Maybe      (fromMaybe)
import           Prelude         hiding (catch)

import           Compiler.Simple

-- A program can exit normaly, due to an uncaught escape, or due to calling undefined.

data Status =
   ExitStatus
 | EscapeStatus Ident Value
 | UndefinedStatus
 | WriteStatus String Status

data Value =
   ClosureValue { closureValue :: Value -> M Value }
 | ConstructorValue { constructorIndex :: Int, constructorValues :: [Value] }
 | StringValue { stringValue :: String }
 | TupleValue { tupleValues :: [Value] }
 | UnitValue

type Env = IntMap Value
type G = IntMap Fun

interpret :: Program -> Status
interpret (Program _ _ xs d) = run xs $ do
  t <- getFun d
  eval t

eval :: Term -> M Value
eval t =
  case t of
    ApplyTerm t1 t2 -> do
      v1 <- eval t1
      v2 <- eval t2
      closureValue v1 v2
    BindTerm d t1 t2 -> do
      v1 <- eval t1
      bind [(d, v1)] (eval t2)
    CaseTerm t1 rs -> do
      v <- eval t1
      let (ds, t2) = rs !! constructorIndex v
      bind (zip ds (constructorValues v)) (eval t2)
    CatchTerm d1 t1 d2 d3 t2 ->
      catch d1 (eval t1) (\ v1 v2 -> bind [(d2, v1), (d3, v2)] (eval t2))
    ConcatenateTerm t1 t2 -> do
      v1 <- eval t1
      v2 <- eval t2
      return $ StringValue (stringValue v1 ++ stringValue v2)
    ConstructorTerm _ i ts -> do
      vs <- mapM eval ts
      return $ ConstructorValue i vs
    FunTerm d -> do
      t <- getFun d
      withEnv emptyEnv (eval t)
    LambdaTerm d _ t -> do
      r <- getEnv
      return $ ClosureValue (\ v -> withEnv r (bind [(d, v)] (eval t)))
    StringTerm s ->
      return $ StringValue s
    ThrowTerm d t -> do
      v <- eval t
      throw d v
    TupleTerm ts -> do
      vs <- mapM eval ts
      return $ TupleValue vs
    UnitTerm ->
      return UnitValue
    UnreachableTerm _ ->
      runUnreachable
    UntupleTerm ds t1 t2 -> do
      v1 <- eval t1
      bind (zip ds (tupleValues v1)) (eval t2)
    VariableTerm d ->
      getValue d

emptyEnv :: Env
emptyEnv = IntMap.empty

bind :: [(Ident, Value)] -> M a -> M a
bind ps m = do
  r <- getEnv
  withEnv (foldl (\ r (d, v) -> IntMap.insert d v r) r ps) m

getValue :: Ident -> M Value
getValue d = do
  r <- getEnv
  return $ fromMaybe (unreachable "getValue") (IntMap.lookup d r)

getFun :: Ident -> M Term
getFun d = do
  g <- getG
  let Fun _ t = fromMaybe (unreachable "getFun") (IntMap.lookup d g)
  return t

newtype M a = M { runM :: G -> Env -> K a -> K1 -> K2 -> Status }

newtype K a = K { runK :: a -> K1 -> K2 -> Status }

newtype K1 = K1 { runK1 :: Value -> Status }

newtype K2 = K2 { runK2 :: Ident -> K Value -> Value -> Status }

instance Monad M where
  return x = M (\ _ _ k k1 k2 -> runK k x k1 k2)
  m >>= f = M (\ g r k -> runM m g r (K $ \ x -> runM (f x) g r k))

run :: G -> M Value -> Status
run g m = runM m g emptyEnv emptyK emptyK1 emptyK2

emptyK :: K Value
emptyK = K $ \ v k1 _ -> runK1 k1 v

emptyK1 :: K1
emptyK1 = K1 $ const ExitStatus

emptyK2 :: K2
emptyK2 = K2 $ \ d k v -> EscapeStatus d v

runUnreachable :: M Value
runUnreachable = M $ \ _ _ _ _ _ -> UndefinedStatus

throw :: Ident -> Value -> M Value
throw d v = M $ \ _ _ k _ k2 -> runK2 k2 d k v

catch :: Ident -> M Value -> (Value -> Value -> M Value) -> M Value
catch d1 m f = M $ catch' d1 m f

catch' :: Ident -> M Value -> (Value -> Value -> M Value) -> G -> Env -> K Value -> K1 -> K2 -> Status
catch' d1 m f g r k k1 k2 = runM m g r emptyK (K1 $ \ v -> runK k v k1 k2) (K2 check)
  where check d2 k' v | d1 == d2  = let c = ClosureValue $ \ v -> M $ \ _ _ k k1' k2'-> runK k' v (K1 $ \ v' -> runK k v' k1' k2') k2'
                                     in runM (f c v) g r emptyK (K1 $ \ v -> runK k v k1 k2) (K2 check)
                      | otherwise = runK2 k2 d2 (K $ \ v k1' k2' -> runK k' v (K1 $ \ v' -> runK k v' k1' k2') k2') v

withEnv :: Env -> M a -> M a
withEnv r m = M $ \ g _ -> runM m g r

getEnv :: M Env
getEnv = M $ \ _ r k -> runK k r

getG :: M G
getG = M $ \ g _ k -> runK k g

todo :: String -> a
todo s = error $ "todo: Interpreter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Interpreter." ++ s
