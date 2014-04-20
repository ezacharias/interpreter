-- The language stripped of syntactic sugar. Polymorphism has been eliminated.
-- The module system has been eliminated. All variables use integers rather than strings.
module Compiler.Simple where


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

-- Functions are actually called with no arguments. Hence, they are just a
-- return type and a term. To take an argument, the term returns a lambda
-- expression.
data Fun = Fun Type Term
   deriving (Eq, Ord, Show)

data Type =
   ArrowType Type Type
 | StringType
 | TupleType [Type]
 | UnitType
 | SumType Ident
   deriving (Eq, Ord, Show)

-- Let's go over the terms one at a time.
--
--   ApplyTerm
--
-- Calls the lambda function with the value.
--
--   BindTerm
--
-- Binds a variable to a value in the final term.
--
--   CatchTerm tag ident term
--
-- Evaluates term. Returns a stream of type ident. If it escapes with tag,
-- returns Next. Otherwise returns End.
--
--   ConcatenateTerm
--
-- String concatenation.
--
--   ConstructorTerm sum idx terms
--
-- Creates a constructor of the sum type with the constructor index and the
-- results of the terms as elements.
--
--   FunTerm
--
-- Evaluates the top-level function.
--
--   LambdaTerm var type term
--
-- Return a lambda function. The type is the type of the parameter.
--
--   StringTerm
--
-- A string literal.
--
--   ThrowTerm tag term
--
-- Escapes using the tag and the result of term.
--
--   TupleTerm
--
-- Creates a tuple.
--
--   UnitTerm
--
-- Tuples of 0 or 1 element are not permitted, so units are used.
--
--   UnreachableTerm
--
-- The program exits immediately if unreachable is evaluated.
--
--   UntupleTerm
--
--  Binds the elements in the tuple.
--
--    VariableTerm
--
--  Returns the value of the variable binding.
data Term =
   ApplyTerm Term Term
 | BindTerm Ident Term Term
 | CaseTerm Term [([Ident], Term)]
 | CatchTerm Ident Ident Term
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
