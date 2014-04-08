module Compiler.Direct where

import Data.IntMap (IntMap)

type Ident = Int
type IdentMap a = IntMap a
type Index = Int

-- A program is a set of sum type declarations, function declarations, and a
-- main function.
data Program = Program
 { programSums :: IdentMap Sum
 , programFuns :: IdentMap Fun
 , programMain :: Ident
 } deriving (Eq, Ord, Show)

data Sum = Sum [[Type]]
   deriving (Eq, Ord, Show)

data Fun = Fun [Ident] [Type] Term
   deriving (Eq, Ord, Show)

data Type =
   StringType
 | TupleType [Type]
 | SumType Ident
   deriving (Eq, Ord, Show)

data Term =
   CallTerm Ident [Ident]
 | CaseTerm Ident [([Ident], Term)]
 | ConcatenateTerm Ident Ident (Ident, Term)
 | ConstructorTerm Ident Index [Ident] (Ident, Term)
 -- ^ The first ident is the type ident
 | StringTerm String (Ident, Term)
 | TupleTerm [Ident] (Ident, Term)
 | UnreachableTerm Type ()
 | UntupleTerm Ident ([Ident], Term)
 | WriteTerm Ident (Term)
   deriving (Eq, Ord, Show)
