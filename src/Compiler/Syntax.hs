module Compiler.Syntax where

import qualified Compiler.Type as Type

data Program = Program [Dec]
               deriving (Eq, Show)

type Name = (String, [Type])
type Path = [Name]

-- Fix sub
data Dec = FunDec Pos [Type.Type] Type.Type String [String] [Pat] Type Term
         -- ^ Types of parameterns and return type.
         | ModDec Pos String [String] [Dec]
         | NewDec Pos Type.Path String [String] Path
         -- ^ Global path
         | SubDec Pos String [String] Path
         | SumDec Pos String [String] [(Pos, String, [Type])]
         | UnitDec Pos String [String] [Dec]
           deriving (Eq, Show)

data Term = ApplyTerm Type.Type Term Term
          -- ^ Metavariable for type of the argument.
          | AscribeTerm Pos Term Type
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

data Pat = AscribePat Pos Pat Type
         | LowerPat Pos String
         | TuplePat Pos [Type.Type] [Pat]
          -- ^ Metavariables for the types of the elements.
         | UnderbarPat
         | UnitPat Pos
         | UpperPat Pos Type.Path [Type.Type] Type.Type Path [Pat]
          -- ^ Full path of the constructor, constructor argument types, constructor return type.
           deriving (Eq, Show)

data Type = ArrowTyp Type Type
         | LowerTyp String
         | TupleTyp [Type]
         | UnitTyp Pos
         | UpperTyp Pos Type.Path Path
         -- ^ Full path.
           deriving (Eq, Show)

-- | Position filename line col.

data Pos = Pos String Int Int
           deriving (Eq, Show)

funType :: [Pat] -> Type -> Type.Type
funType []     t = typeType t
funType (p:ps) t = Type.Arrow (patType p) (funType ps t)

-- | This can only be used for patterns required to be fully typed.
patType :: Pat -> Type.Type
patType (AscribePat _ p ty) = typeType ty -- not sure about this
patType (LowerPat _ s)    = error "Compiler.Syntax.patType"
patType (TuplePat _ _ ps) = Type.Tuple (map patType ps)
patType UnderbarPat       = error "Compiler.Syntax.patType"
patType (UnitPat _)       = Type.Unit
patType (UpperPat _ _ _ _ _ _) = error "Syntax.patType: not yet supported"

typeType :: Type -> Type.Type
typeType (ArrowTyp ty1 ty2)  = Type.Arrow (typeType ty1) (typeType ty2)
typeType (LowerTyp s)        = Type.Variable s
typeType (TupleTyp tys)      = Type.Tuple (map typeType tys)
typeType (UnitTyp _)         = Type.Unit
typeType (UpperTyp _ _ [("String", [])]) = Type.String -- fix this
typeType (UpperTyp _ _ q) = Type.Variant (createPath q)

createPath :: Path -> Type.Path
createPath q = Type.Path (map f q)
  where f (s, tys) = Type.Name s (map typeType tys)
