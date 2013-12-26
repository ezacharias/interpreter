-- The language stripped of syntactic sugar. Some names are kept to implement show.

module Compiler.Lambda where

type TagIdent = Int
type VariantIdent = Int
type ConstructorIndex = Int
type FunctionIdent = Int
type TypeIdent = Int
type ValueIdent = Int

data Program = Program [(TagIdent, Tag)] [(VariantIdent, Variant)] [(FunctionIdent, Function)] FunctionIdent
               deriving (Eq, Show)

data Tag = Tag Type Type
           deriving (Eq, Show)

-- We store the names of constructors so we can implement 'show' in the interpreter.

data Variant = Variant [TypeIdent] [String] [[Type]]
               deriving (Eq, Show)

data Function = Function [TypeIdent] Type Term
                deriving (Eq, Show)

functionBody :: Function -> Term
functionBody (Function _ _ e) = e

-- Evaluating a type eliminates the type variables.

data Type = ArrowType Type Type
          | StringType
          | TagType Type Type
          | TupleType [Type]
          | UnitType
          | VariableType TypeIdent
          | VariantType VariantIdent [Type]
            deriving (Eq, Show)

data Term = ApplyTerm Term Term
          | BindTerm ValueIdent Term Term
       -- | CaseTerm Term [([ValueIdent], Term)]
          | CatchTerm Term Term ValueIdent ValueIdent Term
          | ConstructorTerm VariantIdent [Type] ConstructorIndex [Term]
          | IsEqualTerm Type Term Term
          | LambdaTerm ValueIdent Type Term
          | ProtectTerm Term Term
          | ShowTerm Type Term
          | StringTerm String
          | TagTerm TagIdent
          | TestTerm Term ConstructorIndex [ValueIdent] Term Term
          | ThrowTerm Term Term
          | TupleTerm [Term]
          | TypeApplyTerm FunctionIdent [Type]
          | UnitTerm
          | Unreachable Type
          | UntupleTerm [ValueIdent] Term Term
          | VariableTerm ValueIdent
            deriving (Eq, Show)
