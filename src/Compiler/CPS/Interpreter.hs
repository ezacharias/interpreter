module Compiler.CPS.Interpreter where

import Compiler.CPS

-- A program can exit normaly, due to an uncaught escape, or due to calling undefined.

data Status =
   ExitStatus
 | EscapeStatus Ident Value
 | UndefinedStatus
 | WriteStatus String Status
   deriving (Show)

data Value =
   ClosureValue { closureValue :: [Value] -> M Status }
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

interpret :: Program -> Status
interpret p = run p $ do
  (ds, t) <- getFun (programMain p)
  bind ds [ ClosureValue $ \ [v, h] -> closureValue h [v]
          , ClosureValue $ \ [v] -> return ExitStatus
          ] $
    eval t

run :: Program -> M a -> a
run = undefined

eval :: Term -> M Status
eval t =
  case t of
    ApplyTerm d ds -> do
      x <- getValue d
      xs <- mapM getValue ds
      closureValue x xs
 -- CallTerm Ident [Ident]
    CallTerm d1 d2s -> do
      (d3s, t1) <- getFun d1
      v2s <- mapM getValue d2s
      withEnv emptyEnv $
        bind d3s v2s $
          eval t1
    CaseTerm d1 r1s -> do
      v1 <- getValue d1
      let (d2s, t2) = r1s !! constructorIndex v1
      bind d2s (constructorValues v1) $
        eval t2
    ConcatenateTerm d1 d2 d3 t1 -> do
      v2 <- getValue d2
      v3 <- getValue d3
      bind [d1] [StringValue (stringValue v2 ++ stringValue v3)] $
        eval t1
    ConstructorTerm d1 d2 i1 d3s t1 -> do
      v3s <- mapM getValue d3s
      bind [d1] [ConstructorValue i1 v3s] $
        eval t1
    LambdaTerm d ds _ t1 t2 -> do
      r <- getEnv
      bind [d] [ClosureValue (\ vs -> withEnv r (bind ds vs (eval t1)))] $
        eval t2
    StringTerm d1 s1 t1 -> do
      bind [d1] [StringValue s1] $
        eval t1
    TupleTerm d1 d2s t1 -> do
      v2s <- mapM getValue d2s
      bind [d1] [TupleValue v2s] $
        eval t1
    UnreachableTerm ->
      return UndefinedStatus
    UntupleTerm d1s d2 t1 -> do
      v2s <-  getValue d2
      bind d1s (tupleValues v2s) $
        eval t1

type Env = ()

emptyEnv :: Env
emptyEnv = undefined

getFun :: Ident -> M ([Ident], Term)
getFun = undefined

getValue :: Ident -> M Value
getValue = undefined

withEnv :: Env -> M a -> M a
withEnv = undefined

bind :: [Ident] -> [Value] -> M a -> M a
bind = undefined

getEnv :: M Env
getEnv = undefined

type M a = [a]
