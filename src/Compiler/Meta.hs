module Compiler.Meta where

import           Data.Maybe      (fromJust)

import           Compiler.Syntax
import qualified Compiler.Type   as Type

-- Add type metavariables to the syntax. This is done before type checking.
-- We also add the type to every upper-case variable so the type-checker does
-- not have to look it up.

data Result a = Normal a
              | Next         (Int -> Result a)
              | Arity String (([String], Type.Type) -> Result a)

instance Monad Result where
  return = Normal
  Normal x  >>= f = f x
  Next k    >>= f = Next    (\ x -> k x >>= f)
  Arity s k >>= f = Arity s (\ x -> k x >>= f)

env :: [(String, ([String], Type.Type))]
env = [("Exit", ([], Type.Variant "Output" []))]

addMetavariables :: Program -> Program
addMetavariables (Program ds) = Program (reverse ds')
  where r = foldl arity env ds
        (ds', _) = foldl f ([], 0) ds
        f :: ([Dec], Int) -> Dec -> ([Dec], Int)
        f (ds', n) d = dec ds' r n d

arity :: [(String, ([String], Type.Type))] -> Dec -> [(String, ([String], Type.Type))]
arity r (FunDec _ s ss ps ty _) = (s, (ss, funType ps ty)) : r

genMeta :: a -> Result Type.Type
genMeta _ = Next (Normal . Type.Metavariable)

-- data Dec = FunDec Pos String [String] [Pat] Typ Term
dec :: [Dec] -> [(String, ([String], Type.Type))] -> Int -> Dec -> ([Dec], Int)
dec ds r n (FunDec pos s ss ps t e) = check n m
  where m = do ps' <- mapM pat ps
               t' <- term e
               return $ FunDec pos s ss ps' t t' : ds
        check n (Normal e)  = (e, n)
        check n (Next k)    = check (n + 1) (k n)
        check n (Arity s k) = check n (k (lookupJust s r))

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
term (SeqTerm t1 t2)      = do t1' <- term t1
                               t2' <- term t2
                               return $ SeqTerm t1' t2'
term (TupleTerm p ts es)  = do ts' <-  mapM genMeta ts
                               es' <- mapM term es
                               return $ TupleTerm p ts' es'
term (UnitTerm p)         = return $ UnitTerm p
term (UpperTerm p _ _ s)  = do (ss, ty) <- Arity s Normal
                               ts' <- mapM genMeta ss
                               ty' <- return $ Type.rename (zip ss ts') ty
                               return $ UpperTerm p ts' ty' s
term (VariableTerm p s)   = return $ VariableTerm p s

pat :: Pat -> Result Pat
pat (AscribePat p ty) = do p' <- pat p
                           return $ AscribePat p' ty
pat (LowerPat x)      = return $ LowerPat x
pat (TuplePat ms ps)  = do ms' <- mapM genMeta ms
                           ps' <- mapM pat ps
                           return $ TuplePat ms' ps'
pat UnderbarPat       = return UnderbarPat
pat (UnitPat pos)     = return $ UnitPat pos

-- Utility

lookupJust :: Eq a => a -> [(a, b)] -> b
lookupJust key = fromJust . lookup key
