module Compiler.Interpreter where

import           Control.Monad   (zipWithM)
import           Data.Maybe      (fromJust)

import           Compiler.Lambda

data Value = VariantValue ConstructorIndex [Value]
           | UnitValue
           | StringValue String
           | TagValue { tagValue :: TagIdent }
           | TupleValue { tupleValue :: [Value] }
           | ClosureValue { closureValue :: (Value -> Result Value) }

variantValue :: Value -> (ConstructorIndex, [Value])
variantValue (VariantValue d vs) = (d, vs)
variantValue _ = error "Compiler.Interpreter.variantValue"

instance Show Value where
  show (VariantValue n vs) = "variant"
  show UnitValue           = "unit"
  show (StringValue _)     = "string"
  show (TagValue _)        = "tag"
  show (TupleValue _)      = "tuple"
  show (ClosureValue _)    = "closure"

instance Eq Value where
  VariantValue n1 vs1 == VariantValue n2 vs2 = n1 == n2 && vs1 == vs2
  UnitValue           == UnitValue           = True
  StringValue s1      == StringValue s2      = s1 == s2
  TagValue d1         == TagValue d2         = d1 == d2
  TupleValue vs1      == TupleValue vs2      = vs1 == vs2
  _ == _ = error "Eq Value"

-- This is what can result from evaluating a term.

data Result a = Normal a
              | Escape TagIdent Value (Value -> Result a)
              | LookupFunction FunctionIdent (Function -> Result a)
              | LookupTag TagIdent (Tag -> Result a)
              | LookupVariant VariantIdent (Variant -> Result a)
              | GetTypeEnvironment ([(TypeIdent, Type)] -> Result a)
              | GetValueEnvironment ([(ValueIdent, Value)] -> Result a)

instance Show a => Show (Result a) where
  show (Normal x)              = "normal: " ++ show x
  show (Escape _ _ _)          = "escape"
  show (LookupFunction _ _)    = "lookup function"
  show (LookupTag _ _)         = "lookup tag"
  show (LookupVariant _ _)     = "lookup variant"
  show (GetTypeEnvironment _)  = "get type environment"
  show (GetValueEnvironment _) = "get value environment"

instance Monad Result where
  return = Normal
  Normal x              >>= f = f x
  Escape t v k          >>= f = Escape t v (\ x -> k x >>= f)
  LookupFunction d k    >>= f = LookupFunction d (\ x -> k x >>= f)
  LookupTag d k         >>= f = LookupTag d (\ x -> k x >>= f)
  LookupVariant d k     >>= f = LookupVariant d (\ x -> k x >>= f)
  GetTypeEnvironment k  >>= f = GetTypeEnvironment (\ x -> k x >>= f)
  GetValueEnvironment k >>= f = GetValueEnvironment (\ x -> k x >>= f)

-- A program can exit normaly, due to an uncaught escape, or due to calling undefined.

data Status = ExitStatus
            | EscapeStatus TagIdent Value
            | UndefinedStatus
            | WriteStatus String Status

-- The interpreter returns a list of strings and an exit status.

interpret :: Program -> Status
interpret (Program ts ns fs d) = loop ts ns fs r
                                 where r = do v <- eval (functionBody (lookupJust d fs))
                                              (closureValue v) UnitValue

loop :: [(TagIdent, Tag)] -> [(VariantIdent, Variant)] -> [(FunctionIdent, Function)] -> Result Value -> Status
loop ts ns fs r = loop1 r
  where loop1 (Normal x) = loop2 x
        loop1 (Escape tag x k) = EscapeStatus tag x
        loop1 (LookupTag d k) = loop1 $ k (lookupJust d ts)
        loop1 (LookupVariant d k) = loop1 $ k (lookupJust d ns)
        loop1 (LookupFunction d k) = loop1 $ k (lookupJust d fs)
        loop1 (GetTypeEnvironment k) = loop1 $ k []
        loop1 (GetValueEnvironment k) = loop1 $ k []
        exitIndex = 0
        writeIndex = 1
        continueIndex = 2
        loop2 (VariantValue d [])                 | d == exitIndex     = ExitStatus
        loop2 (VariantValue d [StringValue s, v]) | d == writeIndex    = WriteStatus s $ loop2 v
        loop2 (VariantValue d [ClosureValue k])   | d == continueIndex = loop1 $ k UnitValue
        loop2 _ = error "Compiler.Interpreter.loop: impossible"

-- Add the function to the front of any continuation.

warp :: (Result Value -> Result Value) -> Result Value -> Result Value
warp f (Normal x)              = Normal x
warp f (Escape tag x k)        = Escape tag x (f . k)
warp f (LookupFunction d k)    = LookupFunction d (f . k)
warp f (LookupTag d k)         = LookupTag d (f . k)
warp f (LookupVariant d k)     = LookupVariant d (f . k)
warp f (GetTypeEnvironment k)  = GetTypeEnvironment (f . k)
warp f (GetValueEnvironment k) = GetValueEnvironment (f . k)

withDynamicEnvironment :: [(TypeIdent, Type)] -> [(ValueIdent, Value)] -> Result a -> Result a
withDynamicEnvironment xs ys (Normal x)              = Normal x
withDynamicEnvironment xs ys (Escape t v k)          = Escape t v (withDynamicEnvironment xs ys . k)
withDynamicEnvironment xs ys (LookupFunction d k)    = LookupFunction d (withDynamicEnvironment xs ys . k)
withDynamicEnvironment xs ys (LookupTag d k)         = LookupTag d (withDynamicEnvironment xs ys . k)
withDynamicEnvironment xs ys (LookupVariant d k)     = LookupVariant d (withDynamicEnvironment xs ys . k)
withDynamicEnvironment xs ys (GetTypeEnvironment k)  = withDynamicEnvironment xs ys $ k xs
withDynamicEnvironment xs ys (GetValueEnvironment k) = withDynamicEnvironment xs ys $ k ys

eval :: Term -> Result Value
eval (ApplyTerm e1 e2)          = do { v1 <- eval e1; v2 <- eval e2; (closureValue v1) v2 }
eval (BindTerm d e1 e2)         = do { v1 <- eval e1; bind [d] [v1] e2 }
-- eval (CaseTerm e cs)            = do { v <- eval e; evalCase cs (variantValue v) }
eval (CatchTerm e1 d e2 e3)     = do { tag <- eval e1; evalCatchTerm (tagValue tag) d e2 (eval e3) }
eval (ConstructorTerm _ _ d es) = mapM eval es >>= Normal . VariantValue d
eval (IsEqualTerm t e1 e2)      = do { t' <- evalType t; v1 <- eval e1; v2 <- eval e2; evalIsEqualTerm t' v1 v2 }
eval (LambdaTerm d t e)         = Normal $ ClosureValue (\ v -> bind [d] [v] e)
eval (ProtectTerm e1 e2)        = protect e2 (eval e1)
eval (StringTerm s)             = Normal $ StringValue s
eval (TagTerm d)                = Normal $ TagValue d
eval (TestTerm t1 i1 ds t2 t3)  = do t1' <- eval t1
                                     case t1' of
                                       VariantValue i2 vs
                                         | i1 == i2  -> bind ds vs t2
                                         | otherwise -> eval t3
                                       _ -> error "unreachable"
eval (ThrowTerm e1 e2)          = do { v1 <- eval e1; v2 <- eval e2; Escape (tagValue v1) v2 Normal }
eval (TupleTerm ts)             = mapM eval ts >>= Normal . TupleValue
eval (TypeApplyTerm d ts)       = do { ts' <- mapM evalType ts; LookupFunction d $ typeApplyTerm ts' }
eval (ShowTerm t e)             = do { t' <- evalType t; v <- eval e; evalShowValue t' v }
eval UnitTerm                   = Normal UnitValue
eval (Unreachable _)            = error "Interpreter: Unreachable"
eval (UntupleTerm ds e1 e2)     = do { v <- eval e1; bind ds (tupleValue v) e2 }
eval (VariableTerm d)           = GetValueEnvironment (Normal . lookupJust d)

bind :: [ValueIdent] -> [Value] -> Term -> Result Value
bind ds vs e = do xs <- GetTypeEnvironment Normal
                  ys <- GetValueEnvironment Normal
                  withDynamicEnvironment xs (zip ds vs ++ ys) (eval e)

evalCase :: [([ValueIdent], Term)] -> (ConstructorIndex, [Value]) -> Result Value
evalCase cs (n, vs) = bind ds vs e'
                      where (ds, e') = cs !! n

evalCatchTerm :: TagIdent -> ValueIdent -> Term -> Result Value -> Result Value
evalCatchTerm tag1 d e r = check r
  where check (Escape tag2 v k) | tag1 == tag2 = bind [d] [TupleValue [v, ClosureValue (check . k)]] e
        check x = warp check x

evalIsEqualTerm :: Type -> Value -> Value -> Result Value
evalIsEqualTerm t v1 v2 = if v1 == v2
                            then return $ VariantValue 0 []
                            else return $ VariantValue 1 []

protect :: Term -> Result Value -> Result Value
protect e2 (Escape t v k) = eval e2
protect e2 x              = warp (protect e2) x

typeApplyTerm :: [Type] -> Function -> Result Value
typeApplyTerm ts (Function ds _ e) = check $ eval e
                                     where check (GetTypeEnvironment k) = k (zip ds ts)
                                           check x                      = warp check x

evalShowValue :: Type -> Value -> Result Value
evalShowValue t v = do s <- showValue t v
                       Normal (StringValue s)
  where showValue t (VariantValue d2 vs) = showVariantValue t d2 vs
        showValue t UnitValue = return "()"
        showValue t (StringValue s) = return $ "\"" ++ s ++ "\""
        showValue t (TagValue d) = showTagValue t d
        showValue t (TupleValue vs) = showTupleValue t vs
        showValue t (ClosureValue f) = return "<closure>"
        showVariantValue (VariantType d1 ts) d2 vs = do Variant _ ss tss <- LookupVariant d1 Normal
                                                        s1 <- return (ss !! d2)
                                                        s2 <- zipWithM parens ts vs
                                                        Normal (s1 ++ concat s2)
        showVariantValue _ _ _ = error "impossible"
        showTagValue _ d = do Tag s _ _ <- LookupTag d Normal
                              return s
        showTupleValue (TupleType (t:ts)) (v:vs) = do s1 <- showValue t v
                                                      s2 <- commas ts vs
                                                      return $ "(" ++ s1 ++ s2
        showTupleValue _ _ = error "impossible"
        parens t v = do s <- showValue t v
                        return $ "(" ++ s ++ ")"
        commas [] [] = return ")"
        commas (t:ts) (v:vs) = do s1 <- showValue t v
                                  s2 <- commas ts vs
                                  return $ ", " ++ s1 ++ s2
        commas _ _ = error "impossible"

evalType :: Type -> Result Type
evalType (ArrowType t1 t2) = do t1' <- evalType t1
                                t2' <- evalType t2
                                return $ ArrowType t1' t2'
evalType StringType = return StringType
evalType (TagType t1 t2) = do t1' <- evalType t1
                              t2' <- evalType t2
                              return $ TagType t1' t2'
evalType (TupleType ts) = do ts' <- mapM evalType ts
                             return $ TupleType ts'
evalType UnitType = return UnitType
evalType (VariableType d) = GetTypeEnvironment (Normal . lookupJust d)
evalType (VariantType n ts) = do ts' <- mapM evalType ts
                                 return $ VariantType n ts'

-- Used for testing.

evalClosed :: Term -> Result Value
evalClosed e = withDynamicEnvironment [] [] (eval e)

-- Utility

lookupJust :: Eq a => a -> [(a, b)] -> b
lookupJust key = fromJust . lookup key
