module Compiler.Syntax where

import qualified Compiler.Type as Type


data Program = Program [Dec]
               deriving (Eq, Show)

type Name = (String, [Type])
type Path = [Name]

data Dec = FunDec Pos [Type.Type] Type.Type String [String] [Pat] Type Term
         -- ^ Types of parameterns and return type.
         | ModDec Pos String [String] [Dec]
         | NewDec Pos Type.Path String [String] Path
         -- ^ Global path
         | SubDec Pos Type.Path String [String] Path
         -- ^ Global path
         | SumDec Pos Type.Path String [String] [(Pos, [Type.Type], String, [Type])]
         | UnitDec Pos String [String] [Dec]
           deriving (Eq, Show)

data Term = ApplyTerm Type.Type Term Term
          -- ^ Metavariable for type of the argument.
          | AscribeTerm Pos Type.Type Term Type
          -- ^ Type of the type expression.
          | BindTerm Type.Type Pat Term Term
          -- ^ Metavariable for type of the LHS.
          | CaseTerm Type.Type Term [Rule]
          -- ^ Metavariable for result type.
          | ForTerm [Type.Type] Type.Type [Pat] Term Term
          -- ^ Metavariables for pattern types and LHS.
          | SeqTerm Term Term
          | StringTerm Pos String
          | TupleTerm Pos [Type.Type] [Term]
          -- ^ Metavariables for types of the elements.
          | UnitTerm Pos
          | UpperTerm Pos Type.Path Type.Type Path
          -- ^ Full path and type.
          | VariableTerm Pos String
            deriving (Eq, Show)

type Rule = (Pat, Term)

data Pat = AscribePat Pos Type.Type Pat Type
         -- ^ Type returned by the ascription.
         | LowerPat Pos String
         | TuplePat Pos [Type.Type] [Pat]
          -- ^ Metavariables for the types of the elements.
         | UnderbarPat
         | UnitPat Pos
         | UpperPat Pos Type.Path [Type.Type] Type.Type Path [Pat]
          -- ^ Full path of the constructor, constructor argument types, constructor return type.
           deriving (Eq, Show)

data Type = ArrowType Type Type
         | LowerType String
         | TupleType [Type]
         | UnitType Pos
         | UpperType Pos Path
           deriving (Eq, Show)

-- | Position filename line col.

data Pos = Pos String Int Int
           deriving (Eq, Show)
