module Compiler.Direct where

type Ident = Int
type Index = Int

data Program = Program
 { programSums  :: [(Ident, Sum)]
 , programFuns  :: [(Ident, Fun)]
 , programStart :: Ident
 } deriving (Eq, Ord, Show)

data Sum = Sum [[Type]]
   deriving (Eq, Ord, Show)

data Fun = Fun [Ident] [Type] Term
   deriving (Eq, Ord, Show)

data Type =
   StringType
 | TupleType [Type]
 | UnitType
 | SumType Ident
   deriving (Eq, Ord, Show)

data Term =
   CallTerm Ident [Ident]
 | CaseTerm Ident [([Ident], Term)]
 | ConcatenateTerm Ident Ident Ident Term
 | ConstructorTerm Ident Ident Index [Ident] Term
 | ExitTerm
 | StringTerm Ident String Term
 | TupleTerm Ident [Ident] Term
 | UnreachableTerm
 | UntupleTerm [Ident] Ident Term
 | WriteTerm Ident Term
   deriving (Eq, Ord, Show)
