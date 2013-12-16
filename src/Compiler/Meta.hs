module Compiler.Meta where

import Control.Monad (liftM)
import           Data.Maybe      (fromJust)

import           Compiler.Syntax
import qualified Compiler.Type   as Type

-- Add type metavariables to the syntax. This is done before type checking.
-- We also add the type to every upper-case variable so the type-checker does
-- not have to look it up.


data Result a where
  Return      :: a -> Result a
  Bind        :: Result b -> (b -> Result a) -> Result a
  Gen         :: Result Int
  Function    :: String -> Result ([String], Type.Type)
  Constructor :: String -> Result ([String], [Type.Type], Type.Type)

instance Monad Result where
  return = Return
  Return x >>= f = f x
  Bind m g >>= f = Bind m (\ x -> g x >>= f)
  m        >>= f = Bind m f

env :: [(String, ([String], Type.Type))]
env = [ ("Exit", ([], Type.Variant "Output" []))
      , ("Unreachable", (["a"], Type.Variable "a"))
      ]

constructorEnv :: [(String, ([String], [Type.Type], Type.Type))]
constructorEnv = [ ("Exit", ([], [], Type.Variant "Output" []))
                 ]

addMetavariables :: Program -> Program
addMetavariables (Program ds) = Program (reverse ds')
  where r = foldl arity env ds
        g = foldl constructors constructorEnv ds
        (ds', _) = foldl f ([], 0) ds
        f :: ([Dec], Int) -> Dec -> ([Dec], Int)
        f (ds', n) d = dec ds' g r n d

arity :: [(String, ([String], Type.Type))] -> Dec -> [(String, ([String], Type.Type))]
arity r (FunDec _ s ss ps ty _) = (s, (ss, funType ps ty)) : r
arity r (SumDec _ s1 ss rs) = foldl f r rs
                              where f r (_, s2, tys) = (s2, (ss, constructorType tys s1 ss)) : r
arity r (TagDec _ s ty) = (s, ([], typType ty)) : r
arity r (NewDec _ s1 "Escape" [ty1, ty2]) = (s1 ++ ".Catch", (["a"], Type.Arrow (Type.Arrow Type.Unit (Type.Variable "a"))
                                                                    (Type.Arrow (Type.Arrow ty1'
                                                                                (Type.Arrow (Type.Arrow ty2' (Type.Variable "a"))
                                                                                            (Type.Variable "a")))
                                                                                (Type.Variable "a"))))
                                          : (s1 ++ ".Throw", ([], Type.Arrow ty1' ty2'))
                                          : r
                                          where ty1' = typType ty1
                                                ty2' = typType ty2
arity r (NewDec _ _ _ _) = error "NewDec"

constructors :: [(String, ([String], [Type.Type], Type.Type))] -> Dec -> [(String, ([String], [Type.Type], Type.Type))]
constructors r (FunDec _ _ _ _ _ _) = r
constructors r (SumDec _ s1 ss rs) = foldl f r rs
                                     where f r (_, s2, tys) = (s2, (ss, map typType tys, Type.Variant s1 (map Type.Variable ss))) : r
constructors r (TagDec _ _ _) = r
constructors r (NewDec _ _ _ _) = r

genMeta :: a -> Result Type.Type
genMeta _ = liftM Type.Metavariable Gen

-- data Dec = FunDec Pos String [String] [Pat] Typ Term
dec :: [Dec] -> [(String, ([String], [Type.Type], Type.Type))] -> [(String, ([String], Type.Type))] -> Int -> Dec -> ([Dec], Int)
dec ds g r n (FunDec pos s ss ps t e) = check n m
  where m = do ps' <- mapM pat ps
               t' <- term e
               return $ FunDec pos s ss ps' t t' : ds
        check n (Return e)               = (e, n)
        check n (Bind Gen k)             = check (n + 1) (k n)
        check n (Bind (Function s) k)    = check n (k (lookupJust s r))
        check n (Bind (Constructor s) k) = check n (k (lookupJust s g))
        check n (Bind (Return _) _)      = error "Compiler.Meta.dec: unreachable"
        check n (Bind (Bind _ _) _)      = error "Compiler.Meta.dec: unreachable"
dec ds g r n (SumDec pos s ss rs) = (SumDec pos s ss rs : ds, n)
dec ds g r n (TagDec pos s ty)    = (TagDec pos s ty : ds, n)
dec ds g r n (NewDec pos s1 s2 tys) = (NewDec pos s1 s2 tys : ds, n)

term :: Term -> Result Term
term (ApplyTerm _ t1 t2)  = do m <- genMeta ()
                               t1' <- term t1
                               t2' <- term t2
                               return $ ApplyTerm m t1' t2'
term (AscribeTerm p t ty) = do t' <- term t
                               return $ AscribeTerm p t' ty
term (BindTerm _ p t1 t2) = do m <- genMeta ()
                               p <- pat p
                               t1' <- term t1
                               t2' <- term t2
                               return $ BindTerm m p t1' t2'
term (CaseTerm _ t rs)    = do m <- genMeta ()
                               t' <- term t
                               rs' <- mapM rule rs
                               return $ CaseTerm m t' rs'
                            where rule (p, t) = do
                                    p' <- pat p
                                    t' <- term t
                                    return (p', t')
term (SeqTerm t1 t2)      = do t1' <- term t1
                               t2' <- term t2
                               return $ SeqTerm t1' t2'
term (TupleTerm p ts es)  = do ts' <-  mapM genMeta ts
                               es' <- mapM term es
                               return $ TupleTerm p ts' es'
term (UnitTerm p)         = return $ UnitTerm p
term (UpperTerm p _ _ s)  = do (ss, ty) <- Function s
                               ts' <- mapM genMeta ss
                               ty' <- return $ Type.rename (zip ss ts') ty
                               return $ UpperTerm p ts' ty' s
term (VariableTerm p s)   = return $ VariableTerm p s

pat :: Pat -> Result Pat
pat (AscribePat p ty) = do p' <- pat p
                           return $ AscribePat p' ty
pat (LowerPat pos x)  = return $ LowerPat pos x
pat (TuplePat ms ps)  = do ms' <- mapM genMeta ms
                           ps' <- mapM pat ps
                           return $ TuplePat ms' ps'
pat UnderbarPat       = return UnderbarPat
pat (UnitPat pos)     = return $ UnitPat pos
pat (UpperPat pos _ _ x ps)
                      = do (ss, tys, ty) <- Constructor x
                           ss' <- mapM genMeta ss
                           ty' <- return $ Type.rename (zip ss ss') ty
                           tys' <- return $ map (Type.rename (zip ss ss')) tys
                           ps' <- mapM pat ps
                           return $ UpperPat pos tys' ty' x ps'

-- Utility

lookupJust :: Eq a => a -> [(a, b)] -> b
lookupJust key = fromJust . lookup key
