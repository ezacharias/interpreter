module Compiler.Simple where

import Data.IntMap (IntMap)

-- The language stripped of syntactic sugar.

type Ident = Int
type IdentMap a = IntMap a
type Index = Int

data Program = Program
 { programTags :: IdentMap Tag
 , programSums :: IdentMap Sum
 , programFuns :: IdentMap Fun
 , programMain :: Ident
 } deriving (Eq, Ord, Show)

data Tag = Tag Type Type
   deriving (Eq, Ord, Show)

data Sum = Sum [[Type]]
   deriving (Eq, Ord, Show)

data Fun = Fun Type Term
   deriving (Eq, Ord, Show)

data Type =
   ArrowType Type Type
 | StringType
 | TupleType [Type]
 | UnitType
 | SumType Ident
   deriving (Eq, Ord, Show)

data Term =
   ApplyTerm Term Term
 | BindTerm Ident Term Term
 | CaseTerm Term [([Ident], Term)]
 | CatchTerm Ident Term Ident Ident Term
 | ConcatenateTerm Term Term
 | ConstructorTerm Ident Index [Term]
 | FunTerm Ident
 | LambdaTerm Ident Type Term
 | StringTerm String
 | ThrowTerm Ident Term
 | TupleTerm [Term]
 | UnitTerm
 | UnreachableTerm Type
 | UntupleTerm [Ident] Term Term
 | VariableTerm Ident
   deriving (Eq, Ord, Show)
