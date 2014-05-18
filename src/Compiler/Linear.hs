module Compiler.Linear where


type Ident = Int
type Index = Int

-- | We track every tag used in catch and throw as well as every result type
--   used in the body of catch. This is used in CPS conversion.
data Program = Program
             { programTags :: [(Ident, Tag)]
             , programRess :: [Type]
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

data Fun = Fun [Ident] [Type] Type Term
           deriving (Eq, Ord, Show)

data Type = ArrowType Type Type
          | StringType
          | TupleType [Type]
          | SumType Ident
            deriving (Eq, Ord, Show)

data Term =
   ApplyTerm Ident Ident Ident Term
   -- ^ Apply bind closure-ident arg-ident body
 | CallTerm Ident Ident [Ident] Term
 | CaseTerm Ident Ident [([Ident], Term)] Term
 | CatchTerm Ident Ident Type Term Term --
   -- ^ Catch bind tag result-type body1 body2
 | ConcatenateTerm Ident Ident Ident Term
 | ConstructorTerm Ident Ident Index [Ident] Term
 | LambdaTerm Ident Ident Type Term Term
   -- ^ Lambda bind param param-type body1 body2
 | ReturnTerm Ident
 | StringTerm Ident String Term
 | ThrowTerm Ident Ident Ident Term
   -- ^ Throw bind tag arg body
 | TupleTerm Ident [Ident] Term
 | UnreachableTerm Type
 | UntupleTerm [Ident] Ident Term
   deriving (Eq, Ord, Show)
