module Compiler.Syntax where

import qualified Compiler.Type as Type

data Program = Program [Dec]
               deriving (Eq, Show)

type Ident = String

data Dec = FunDec Pos String [String] [Pat] Typ Term
           deriving (Eq, Show)

data Term = ApplyTerm Type.Type Term Term
          | TupleTerm Pos [Type.Type] [Term]
          | UnitTerm Pos
          | UpperTerm Pos [Type.Type] Type.Type String
          | VariableTerm Pos String
            deriving (Eq, Show)

data Pat = UnitPat Pos
           deriving (Eq, Show)

data Typ = UnitTyp Pos
         | UpperTyp Pos String
           deriving (Eq, Show)

-- | Position filename line col.

data Pos = Pos String Int Int
           deriving (Eq, Show)

funType :: [Pat] -> Typ -> Type.Type
funType []     t = typType t
funType (p:ps) t = Type.Arrow (patType p) (funType ps t)

patType :: Pat -> Type.Type
patType (UnitPat _) = Type.Unit

typType :: Typ -> Type.Type
typType (UnitTyp _)       = Type.Unit
typType (UpperTyp _ s) = Type.Variant s []
