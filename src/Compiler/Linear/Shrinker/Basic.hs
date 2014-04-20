-- The only things we need to do in this pass is uncurrying and inlining
-- trivial functions. We can also do any other linear time optimizations,
-- because the more this pass does the less the slower pass will need to
-- do.

module Compiler.Linear.Shrinker.Basic where

-- import Control.Monad (foldM)

import Compiler.Linear

-- Returns the modified program if it has been modified or returns Nothing if
-- there are no modifications.
shrink :: Program -> Maybe Program
shrink p = Nothing -- update (analyze p) p

{-

analyze :: Program -> ()
analyze = undefined

-- First check if the function is curried. Then check if it is trivial.
analyzeFun :: Fun -> ()
analyzeFun = undefined

update :: Analysis -> Program -> Maybe Program
update q (Program x1 x2 x3 d) = if b
                                 then Just (Program x1 x2 x3' d)
                                 else Nothing
  where (x3',b) = run $ foldM ([], False) x3 $ \ (d, x) (xs, b) ->
                    case updateFun x of
                      Nothing -> ((d,x):xs, b)
                      Just x -> ((d,x):xs, True)

data M a = M a

run :: M a -> a
run = undefined

updateFun :: Analysis -> Fun -> Fun
updateFun (Fun d1s ty1s ty2s t1) = undefined

updateTerm :: Term -> M Term
updateTerm t =
  case t of
    --
    ApplyTerm d1s d2 d3s t -- [Ident] Ident [Ident] Term
    -- Lookup the the result of analysis to transform the call.
    CallTerm d1s d2 d3s t -> do -- [Ident] Ident [Ident] Term
      f <- getFun d2
      f d3s d1s t
    --
    CaseTerm d1s d2 c1s t1 -> -- [Ident] Ident [([Ident], Term)] Term
      
    CatchTerm Ident Ident Ident Term Term
    -- ^ CatchTerm tag sumTypeIdent term. Evaluates the term, returning a stream
    --   with the ident.
    ConcatenateTerm Ident Ident Ident Term
    ConstructorTerm Ident Ident Index [Ident] Term
    LambdaTerm Ident [Ident] [Type] Term Term
    ReturnTerm [Ident]
    StringTerm Ident String Term
    ThrowTerm Ident Ident Ident Term
    -- ^ ThrowTerm bind tag arg delim body.
    TupleTerm Ident [Ident] Term
    UnreachableTerm Type
    -- ^ Always a tail-call.
    UntupleTerm [Ident] Ident Term

type Analysis = ()

-}




