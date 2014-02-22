module Compiler.Type where

import Data.Maybe (fromMaybe)

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

pathAddName :: Path -> Name -> Path
pathAddName (Path ns) n = Path (ns ++ [n])

nameAddPath :: Name -> Path -> Path
nameAddPath n (Path ns) = Path (n : ns)

-- Substitute the variables found in the environment.
substitute :: [(String, Type)] -> Type -> Type
substitute r (Arrow t1 t2)    = Arrow (substitute r t1) (substitute r t2)
substitute r (Metavariable n) = Metavariable n
substitute r String           = String
substitute r (Tuple ts)       = Tuple (map (substitute r) ts)
substitute r Unit             = Unit
substitute r (Variable s)     = fromMaybe (Variable s) (lookup s r)
substitute r (Variant q)      = Variant (Path (map (\ (Name s tys) -> Name s (map (substitute r) tys)) (pathNames q)))

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