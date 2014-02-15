module Compiler.Type where

type Metavariable = Int

-- Make sure to modify TypeChecker.unify when changing Type.

data Type = Arrow Type Type
          | Metavariable Metavariable
          | String
          | Tuple { tupleElems :: [Type] }
          | Unit
          | Variable String
          | Variant Path
 deriving (Eq, Ord, Show)

data Name = Name String [Type]
 deriving (Eq, Ord, Show)

data Path = Path { pathNames :: [Name] }
 deriving (Eq, Ord, Show)

rename :: [(String, Type)] -> Type -> Type
rename r (Arrow t1 t2)    = Arrow (rename r t1) (rename r t2)
rename r (Metavariable n) = Metavariable n
rename r String           = String
rename r (Tuple ts)       = Tuple (map (rename r) ts)
rename r Unit             = Unit
rename r (Variable s)     = maybe (Variable s) id (lookup s r)
rename r (Variant q)      = Variant (Path (map (\ (Name s tys) -> Name s (map (rename r) tys)) (pathNames q)))

replace :: Metavariable -> Type -> Type -> Type
replace x t (Arrow t1 t2)    = Arrow (replace x t t1) (replace x t t2)
replace x t (Metavariable n)
                 | x == n    = t
                 | otherwise = Metavariable n
replace x t String           = String
replace x t (Tuple ts)       = Tuple (map (replace x t) ts)
replace x t Unit             = Unit
replace x t (Variable s)     = Variable s
replace x t (Variant q)      = Variant (Path (map (\ (Name s tys) -> Name s (map (replace x t) tys)) (pathNames q)))