module Compiler.Interpreter where

import           Control.Monad   (zipWithM)

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

data Result a where
  Return         :: a -> Result a
  Bind           :: Result b -> (b -> Result a) -> Result a
  Escape         :: TagIdent -> Value -> Result Value
  LookupFunction :: FunctionIdent -> Result Function
  LookupTag      :: TagIdent -> Result String
  LookupVariant  :: VariantIdent -> (Result Variant)
  GetTypeEnv     :: Result [(TypeIdent, Type)]
  GetValueEnv    :: Result [(ValueIdent, Value)]

instance Monad Result where
  return = Return
  Return x >>= f = f x
  Bind m g >>= f = Bind m (\ x -> f =<< g x)
  m        >>= f = Bind m f

instance Show (Result a) where
  show (Return x)         = "normal"
  show (Bind m _)         = show m
  show (Escape _ _)       = "escape"
  show (LookupFunction _) = "lookup function"
  show (LookupTag _)      = "lookup tag"
  show (LookupVariant _)  = "lookup variant"
  show GetTypeEnv         = "get type environment"
  show GetValueEnv        = "get value environment"

-- A program can exit normaly, due to an uncaught escape, or due to calling undefined.

data Status = ExitStatus
            | EscapeStatus TagIdent Value
            | UndefinedStatus
            | WriteStatus String Status

-- The interpreter returns a list of strings and an exit status.

interpret :: Program -> Status
interpret (Program _ ns fs d) = loop ns fs r
  where r = do eval (functionBody (maybe (error "interpreter lookup main") id (lookup d fs)))

loop :: [(VariantIdent, Variant)] -> [(FunctionIdent, Function)] -> Result Value -> Status
loop ns fs r = loop1 r
  where loop1 (Return x) = loop2 x
        loop1 (Bind (Return _) _) = error "Compiler.Interpreter.loop: unreachable"
        loop1 (Bind (Bind _ _) _) = error "Compiler.Interpreter.loop: unreachable"
        loop1 (Bind (Escape tag x) k) = EscapeStatus tag x
        loop1 (Bind (LookupTag d) k) = loop1 $ k "tag"
        loop1 (Bind (LookupVariant d) k) = loop1 $ k (maybe (error "interpreter lookup variant") id (lookup d ns))
        loop1 (Bind (LookupFunction d) k) = loop1 $ k (maybe (error "interpreter lookup function") id (lookup d fs))
        loop1 (Bind GetTypeEnv k) = loop1 $ k []
        loop1 (Bind GetValueEnv k) = loop1 $ k []
        loop1 m = loop1 $ Bind m Return
        exitIndex = 0
        writeIndex = 1
        continueIndex = 2
        loop2 (VariantValue d [])                 | d == exitIndex     = ExitStatus
        loop2 (VariantValue d [StringValue s, v]) | d == writeIndex    = WriteStatus s $ loop2 v
        loop2 (VariantValue d [ClosureValue k])   | d == continueIndex = loop1 $ k UnitValue
        loop2 _ = error "Compiler.Interpreter.loop: impossible"


withDynamicEnv :: [(TypeIdent, Type)] -> [(ValueIdent, Value)] -> Result a -> Result a
withDynamicEnv xs ys m = check m
  where check (Return x)           = Return x
        check (Bind GetTypeEnv k)  = check $ k xs
        check (Bind GetValueEnv k) = check $ k ys
        check (Bind m k)           = Bind m (check . k)
        check m                    = check $ Bind m Return

eval :: Term -> Result Value
eval (ApplyTerm e1 e2)          = do { v1 <- eval e1; v2 <- eval e2; (closureValue v1) v2 }
eval (BindTerm d e1 e2)         = do { v1 <- eval e1; bind [d] [v1] e2 }
-- eval (CaseTerm e cs)            = do { v <- eval e; evalCase cs (variantValue v) }
eval (CatchTerm e1 e2 d1 d2 e3) = do { tag <- eval e1; evalCatchTerm (tagValue tag) (eval e2) d1 d2 e3 }
eval (ConstructorTerm _ _ d es) = mapM eval es >>= Return . VariantValue d
eval (IsEqualTerm t e1 e2)      = do { t' <- evalType t; v1 <- eval e1; v2 <- eval e2; evalIsEqualTerm t' v1 v2 }
eval (LambdaTerm d t e)         = do xs <- GetTypeEnv
                                     ys <- GetValueEnv
                                     Return $ ClosureValue (\ v -> withDynamicEnv xs ((d, v) : ys) (eval e))
eval (ProtectTerm e1 e2)        = protect e2 (eval e1)
eval (StringTerm s)             = Return $ StringValue s
eval (TagTerm d)                = Return $ TagValue d
eval (TestTerm t1 i1 ds t2 t3)  = do t1' <- eval t1
                                     case t1' of
                                       VariantValue i2 vs
                                         | i1 == i2  -> bind ds vs t2
                                         | otherwise -> eval t3
                                       _ -> error "unreachable"
eval (ThrowTerm e1 e2)          = do { v1 <- eval e1; v2 <- eval e2; Escape (tagValue v1) v2 }
eval (TupleTerm ts)             = mapM eval ts >>= Return . TupleValue
eval (TypeApplyTerm d ts)       = do { ts' <- mapM evalType ts; x <- LookupFunction d; typeApplyTerm ts' x }
eval (ShowTerm t e)             = do { t' <- evalType t; v <- eval e; evalShowValue t' v }
eval UnitTerm                   = Return UnitValue
eval (Unreachable _)            = error "Interpreter: Unreachable"
eval (UntupleTerm ds e1 e2)     = do { v <- eval e1; bind ds (tupleValue v) e2 }
eval (VariableTerm d)           = do r <- GetValueEnv
                                     return $ maybe (error "interpreter variable term") id (lookup d r)

bind :: [ValueIdent] -> [Value] -> Term -> Result Value
bind ds vs e = do xs <- GetTypeEnv
                  ys <- GetValueEnv
                  withDynamicEnv xs (zip ds vs ++ ys) (eval e)

evalCase :: [([ValueIdent], Term)] -> (ConstructorIndex, [Value]) -> Result Value
evalCase cs (n, vs) = bind ds vs e'
                      where (ds, e') = cs !! n

evalCatchTerm :: TagIdent -> Result Value -> ValueIdent -> ValueIdent -> Term -> Result Value
evalCatchTerm tag1 r d1 d2 e = check r
  where check (Return x)               = Return x
        check (Bind (Escape tag2 v) k)
                        | tag1 == tag2 = bind [d1, d2] [v, ClosureValue (check . k)] e
        check (Bind m k)               = Bind m (check . k)
        check m                        = check $ Bind m Return

evalIsEqualTerm :: Type -> Value -> Value -> Result Value
evalIsEqualTerm t v1 v2 = if v1 == v2
                            then return $ VariantValue 0 []
                            else return $ VariantValue 1 []

protect :: Term -> Result Value -> Result Value
protect e2 m = check m
  where check (Return x)              = Return x
        check (Bind (Escape tag v) k) = eval e2
        check (Bind m k)              = Bind m (check . k)
        check m                       = check $ Bind m Return

typeApplyTerm :: [Type] -> Function -> Result Value
typeApplyTerm ts (Function ds _ e) = check $ eval e
  where check (Return x)          = Return x
        check (Bind GetTypeEnv k) = check $ k (zip ds ts)
        check (Bind m k)          = Bind m (check . k)
        check m                   = check $ Bind m Return

evalShowValue :: Type -> Value -> Result Value
evalShowValue t v = do s <- showValue t v
                       Return (StringValue s)
  where showValue t (VariantValue d2 vs) = showVariantValue t d2 vs
        showValue t UnitValue = return "()"
        showValue t (StringValue s) = return $ "\"" ++ s ++ "\""
        showValue t (TagValue d) = showTagValue t d
        showValue t (TupleValue vs) = showTupleValue t vs
        showValue t (ClosureValue f) = return "<closure>"
        showVariantValue (VariantType d1 ts) d2 vs = do Variant _ ss tss <- LookupVariant d1
                                                        s1 <- return (ss !! d2)
                                                        s2 <- zipWithM parens ts vs
                                                        Return (s1 ++ concat s2)
        showVariantValue _ _ _ = error "impossible"
        showTagValue _ d = do LookupTag d
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
evalType (VariableType d) = do r <- GetTypeEnv
                               return $ maybe (error "interpreter lookup variable type") id (lookup d r)
evalType (VariantType n ts) = do ts' <- mapM evalType ts
                                 return $ VariantType n ts'

-- Used for testing.

evalClosed :: Term -> Result Value
evalClosed e = withDynamicEnv [] [] (eval e)
