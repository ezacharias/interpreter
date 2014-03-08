module Compiler.SyntaxChecker where

import Data.Either ()

import           Compiler.Syntax

data Env = Env { envSubs :: [(String, [String])]
               , envMods :: [(String, Env)]
               , envSums :: [(String, Int)]
               , envFuns :: [String]
               }

type M a = Either String a

-- Either returns nothing of there were no errors or returns the error string.

syntaxCheckProgram :: Program -> Maybe String
syntaxCheckProgram p = maybeEither m
  where m = Right () {- do r <- programGatherEnv p
               programCheck r p -}

maybeEither :: Either a () -> Maybe a
maybeEither (Left x)   = Just x
maybeEither (Right ()) = Nothing

programGatherEnv :: Program -> M Env
programGatherEnv p = todo

programCheck :: Env -> Program -> M ()
programCheck r (Program ds) = todo -- mapM_ (checkDec r) ds

{-
data Dec = FunDec Pos String [String] [Pat] Typ Term
         | ModDec Pos String [Dec]
         | NewDec Pos String Qual [Typ]
         | SubDec Pos String Qual
         | SumDec Pos String [String] [(Pos, String, [Typ])]
         | UnitDec Pos String [String] [Dec]
           deriving (Eq, Show)
-}

checkDec :: Env -> Dec -> M ()

checkDec r (FunDec p _ _ s _ _ _ _) = todo

checkDec r (ModDec _ _ s ds) = todo -- mapM_ (checkDec (envGetMod r s)) ds

-- We need to check that the unit is bound and that the type arity is correct.
-- Some of this may have been done during gather.

checkDec r (NewDec _ _ s q ts) = todo

-- We simply need to check that the qualified name is bound. We may have already
-- done this when gathering the environment.

checkDec r (SubDec _ _ _ s q) = todo

checkDec r (SumDec _ s ts ds) = todo

-- We need to grab the inner environment. It should already have the lower type
-- bindings added.

checkDec r (UnitDec _ s ss ds) = todo -- mapM_ (checkDec (envGetUnit r s)) ds

-- This cannot fail because we've already computed the top-level.

envGetMod :: Env -> String -> Env
envGetMod = undefined

-- This cannot fail because we've already computed the top-level.

envGetUnit :: Env -> String -> Env
envGetUnit = undefined

-- Hack.

todo :: M a
todo = Right undefined










