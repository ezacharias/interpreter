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
   deriving (Show)

data Result =
   ReturnResult Value
 | EscapeResult (K2 Value) Ident Value

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
interpret (Program _ _ _ xs d) = run (IntMap.fromList xs) $ do
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
    CatchTerm d1 _ t1 ->
      catch d1 (eval t1)
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

newtype M a = M { runM :: G -> Env -> K2 a -> K1 -> Status }

type K2 a = K1 -> a -> Status

type K1 = Result -> Status

instance Monad M where
  return x = M $ \ _ _ k2 k1 -> k2 k1 x
  m >>= f = M $ \ g r k2 k1 -> runM m g r (\ k1 x -> runM (f x) g r k2 k1) k1

emptyEnv :: Env
emptyEnv = IntMap.empty

emptyK2 :: K2 Value
emptyK2 k1 v = k1 (ReturnResult v)

emptyK1 :: G -> K1
emptyK1 g (ReturnResult (ConstructorValue 0 [])) = ExitStatus
emptyK1 g (ReturnResult (ConstructorValue 1 [s, x])) = WriteStatus (stringValue s) (emptyK1 g (ReturnResult x))
emptyK1 g (ReturnResult (ConstructorValue 2 [v])) = run g (closureValue v UnitValue)
emptyK1 g (ReturnResult x) = unreachable $ "emptyK1: " ++ show x
emptyK1 g (EscapeResult _ d v) = EscapeStatus d v

run :: G -> M Value -> Status
run g m = runM m g emptyEnv emptyK2 (emptyK1 g)

throw :: Ident -> Value -> M Value
throw d v = M $ \ _ _ k2 k1 -> k1 (EscapeResult k2 d v)

catch :: Ident -> M Value -> M Value
catch d1 m = M $ catch' d1 m

catch' :: Ident -> M Value -> G -> Env -> K2 Value -> K1 -> Status
catch' d1 m g r k2 k1 = runM m g r emptyK2 (check k2 k1)
  where check k2 k1 (ReturnResult v) = k2 k1 (ConstructorValue 0 [v])
        check k2 k1 (EscapeResult x d2 v1) | d1 == d2 = let v2 = ClosureValue $ \ v -> M $ \ g r k2' k1' -> x (check k2' k1') v
                                                         in k2 k1 (ConstructorValue 1 [v1, v2])
        check k2 k1 (EscapeResult x d2 v1) | otherwise = k1 (EscapeResult (\ k1 v -> x (check k2 k1) v) d2 v1)

runUnreachable :: M Value
runUnreachable = M $ \ _ _ _ _ -> UndefinedStatus

withEnv :: Env -> M a -> M a
withEnv r m = M $ \ g _ -> runM m g r

getEnv :: M Env
getEnv = M $ \ _ r k2 k1 -> k2 k1 r

getG :: M G
getG = M $ \ g _ k2 k1 -> k2 k1 g

todo :: String -> a
todo s = error $ "todo: Interpreter." ++ s

unreachable :: String -> a
unreachable s = error $ "unreachable: Interpreter." ++ s
