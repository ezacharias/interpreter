module Compiler.Interpreter where

import           Data.IntMap     (IntMap)
import qualified Data.IntMap     as IntMap
import           Data.Maybe      (fromMaybe)
import           Prelude         hiding (catch)
import Debug.Trace (trace)

import           Compiler.Simple

-- A program can exit normaly, due to an uncaught escape, or due to calling undefined.

data Status =
   ExitStatus
 | EscapeStatus Ident Value
 | UndefinedStatus
 | WriteStatus String Status
   deriving (Show)

data Value =
   ClosureValue { closureValue :: Value -> M Value }
 | ConstructorValue { constructorIndex :: Int, constructorValues :: [Value] }
 | StringValue { stringValue :: String }
 | TupleValue { tupleValues :: [Value] }
 | UnitValue

instance Show Value where
  show (ClosureValue _) = "closure"
  show (ConstructorValue i vs) = "constructor " ++ show i ++ " " ++ show (length vs)
  show (StringValue s) = s
  show (TupleValue vs) = show (length vs)
  show UnitValue = "()"

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
      trace (show v1) (return ())
      v2 <- eval t2
      closureValue (trace (show v1) v1) v2
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

newtype M a = M { runM :: G -> Env -> K4 -> K3 -> K2 a -> K1 -> Status }

-- The handler for the nearest catch.
type K4 = K3 -> K2 Value -> K1 -> Ident -> Value -> Status

-- The parent handler for the nearest catch.
type K3 = K2 Value -> K1 -> Ident -> Value -> Status

-- The delimited continuation to the nearest catch.
type K2 a = K1 -> a -> Status

-- The continuation of the nearest catch.
type K1 = Value -> Status

instance Monad M where
  return x = M $ \ _ _ _ _ k2 k1 -> k2 k1 x
  m >>= f = M $ \ g r k4 k3 k2 k1 -> runM m g r k4 k3 (\ k1 x -> runM (f x) g r k4 k3 k2 k1) k1

emptyEnv :: Env
emptyEnv = IntMap.empty

emptyK4 :: K4
emptyK4 k3 k2 k1 d v = k3 k2 k1 d v

emptyK3 :: K3
emptyK3 k2 k1 d v = EscapeStatus d v

emptyK2 :: K2 Value
emptyK2 k1 v = k1 v

emptyK1 :: G -> K1
emptyK1 g (ConstructorValue 0 []) = ExitStatus
emptyK1 g (ConstructorValue 1 [s, x]) = WriteStatus (stringValue s) (emptyK1 g x)
emptyK1 g (ConstructorValue 2 [v]) = run g (closureValue v UnitValue)
emptyK1 g _ = unreachable "emtptyK1"

run :: G -> M Value -> Status
run g m = runM m g emptyEnv emptyK4 emptyK3 emptyK2 (emptyK1 g)

throw :: Ident -> Value -> M Value
throw d v = M $ \ _ _ k4 k3 k2 k1 -> k4 k3 k2 k1 d v

catch :: Ident -> M Value -> (Value -> Value -> M Value) -> M Value
catch d1 m f = M $ catch' d1 m f

catch' :: Ident -> M Value -> (Value -> Value -> M Value) -> G -> Env -> K4 -> K3 -> K2 Value -> K1 -> Status
catch' d1 m f g r k4 k3 k2 k1 = runM m g r k4' (k4 k3) emptyK2 (k2 k1)
  where k4' k3' k2' k1' d2 v | d1 == d2 = runM (f v (createClosure k2')) g r k4' k3' emptyK2 k1'
        k4' k3' k2' k1' d2 v | otherwise = k3' k2' k1' d2 v

createClosure :: K2 Value -> Value
createClosure k2 = ClosureValue $ \ v -> M $ \ g r k4' k3' k2' k1' -> k2 (k2' k1') v

-- createContinuation :: K Value -> Value
-- createContinuation k = ClosureValue $ \ v -> M $ \ _ _ k' k1' k2'-> runK k v (K1 $ \ v' -> runK k' v' k1' k2') k2'

runUnreachable :: M Value
runUnreachable = M $ \ _ _ _ _ _ _ -> UndefinedStatus

withEnv :: Env -> M a -> M a
withEnv r m = M $ \ g _ -> runM m g r

getEnv :: M Env
getEnv = M $ \ _ r _ _ k2 k1 -> k2 k1 r

getG :: M G
getG = M $ \ g _ _ _ k2 k1 -> k2 k1 g

todo :: String -> a
todo s = error $ "todo: Interpreter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Interpreter." ++ s
