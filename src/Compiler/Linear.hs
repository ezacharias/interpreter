module Compiler.Linear where

type Ident = Int
type Index = Int

-- A program is a set of tag declarations, sum type declarations, function
-- declarations, and a main function.
data Program = Program
 { programTags :: [(Ident, Tag)]
 , programSums :: [(Ident, Sum)]
 , programFuns :: [(Ident, Fun)]
 , programMain :: Ident
 } deriving (Eq, Ord, Show)

-- The first type is the type of the argument to Throw. The second type is the
-- type of the return from Throw.
data Tag = Tag Type Type
   deriving (Eq, Ord, Show)

-- A sum type contains a list of constructors. Each constructor contains a list
-- of argument types.
data Sum = Sum [[Type]]
   deriving (Eq, Ord, Show)

-- Functions can take more than one argument and have more than one return type.
data Fun = Fun [Ident] [Type] [Type] Term
   deriving (Eq, Ord, Show)

-- Tuples can have 0, 1, or more elements.
data Type =
   ArrowType [Type] [Type]
 | StringType
 | TupleType [Type]
 | SumType Ident
   deriving (Eq, Ord, Show)

-- Should catch do something other than return a stream? I'll need to look into
-- this.

data Term =
   ApplyTerm [Ident] Ident [Ident] Term
 | CallTerm [Ident] Ident [Ident] Term
 | CaseTerm Ident [([Ident], Term)]
   -- ^ The tail of the case becomes a closure which is tail-called by each of
   --   the branches.
 | CatchTerm Ident Ident Ident Term Term
   -- ^ CatchTerm tag sumTypeIdent term. Evaluates the term, returning a stream
   --   with the ident.
 | ConcatenateTerm Ident Ident Ident Term
 | ConstructorTerm Ident Ident Index [Ident] Term
 | LambdaTerm Ident [Ident] [Type] Term Term
 | ReturnTerm [Ident]
 | StringTerm Ident String Term
 | ThrowTerm Ident Ident Ident Term
   -- ^ ThrowTerm bind tag arg body.
 | TupleTerm Ident [Ident] Term
 | UnreachableTerm Type
   -- ^ Always a tail-call.
 | UntupleTerm [Ident] Ident Term
   deriving (Eq, Ord, Show)
