module Compiler.CPS where

import Data.IntMap (IntMap)

type Ident = Int
type IdentMap a = IntMap a
type Index = Int

data Program = Program
 { programSums :: IdentMap Sum
 , programFuns :: IdentMap Fun
 , programMain :: Ident
 } deriving (Eq, Ord, Show)

-- A sum type contains a list of constructors. Each constructor contains a list
-- of argument types.
data Sum = Sum [[Type]]
   deriving (Eq, Ord, Show)

-- Functions take multiple arguments. They do not have return types.
data Fun = Fun [Ident] [Type] Term
   deriving (Eq, Ord, Show)

data Type =
   ClosureType [Type]
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
   ApplyTerm Ident [Ident]
   -- ^ For calling closurs. Tail position.
 | CallTerm Ident [Ident]
   -- ^ For calling top-level functions. Tail position.
 | CaseTerm Ident [([Ident], Term)]
   -- ^ Tail position.
 | ConcatenateTerm Ident Ident Ident Term
 | ConstructorTerm Ident Ident Index [Ident] Term
 | LambdaTerm Ident [Ident] [Type] Term Term
 | StringTerm Ident String Term
 | TupleTerm Ident [Ident] Term
 | UnitTerm Ident Term
 | UnreachableTerm Type
   -- ^ Tail position.
 | UntupleTerm [Ident] Ident Term
   deriving (Eq, Ord, Show)
