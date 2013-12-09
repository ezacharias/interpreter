module Compiler.Type where

type Metavariable = Int

data Type = Arrow Type Type
          | Metavariable Metavariable
          | Tuple [Type]
          | Unit
          | Variable String
          | Variant String [Type]
 deriving (Eq, Show)

rename :: [(String, Type)] -> Type -> Type
rename r (Arrow t1 t2)    = Arrow (rename r t1) (rename r t2)
rename r (Metavariable n) = Metavariable n
rename r (Tuple ts)       = Tuple (map (rename r) ts)
rename r Unit             = Unit
rename r (Variable s)     = maybe (Variable s) id (lookup s r)
rename r (Variant s ts)   = Variant s (map (rename r) ts)

replace :: Metavariable -> Type -> Type -> Type
replace x t (Arrow t1 t2)    = Arrow (replace x t t1) (replace x t t2)
replace x t (Metavariable n)
                 | x == n    = t
                 | otherwise = Metavariable n
replace x t (Tuple ts)       = Tuple (map (replace x t) ts)
replace x t Unit             = Unit
replace x t (Variable s)     = Variable s
replace x t (Variant s ts)   = Variant s (map (replace x t) ts)