module Compiler.CPS where

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
   ArrowType [Type]
 | StringType
 | TupleType [Type]
 | SumType Ident
   deriving (Eq, Ord, Show)

data Term =
   ApplyTerm Ident [Ident]
 | BindTerm Ident Ident Term
 | CallTerm Ident [Ident]
 | CaseTerm Ident [([Ident], Term)]
 | ConcatenateTerm Ident Ident Ident Term
 | ConstructorTerm Ident Ident Index [Ident] Term
 | ExitTerm
 | LambdaTerm Ident [Ident] [Type] Term Term
 | StringTerm Ident String Term
 | TupleTerm Ident [Ident] Term
 | UnreachableTerm
 | UntupleTerm [Ident] Ident Term
 | WriteTerm Ident Term
   deriving (Eq, Ord, Show)
