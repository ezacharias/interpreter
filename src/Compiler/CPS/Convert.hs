module Compiler.CPS.Convert where

import qualified Compiler.CPS as CPS
import qualified Compiler.Simple as Simple

convertTerm :: Simple.Term -> H -> K -> M CPS.Term
convertTerm t h k =
  case t of
    Simple.ApplyTerm t1 t2 ->
      convertTerm t1 h $ \ h d1 ->
        convertTerm t2 h $ \ h d2 ->
          createKClosure k $ \ d3 ->
            createHClosure h $ \ d4 ->
              return $ CPS.ApplyTerm d1 [d2, d3, d4]
    Simple.CaseTerm t1 c1s -> do
      convertTerm t1 h $ \ h d1 -> do
        createKClosure k $ \ d3 ->
          createHClosure h $ \ d4 -> do
            c1s' <- mapM (convertRule (createH d4) (createK d3)) c1s
            return $ CPS.CaseTerm d1 c1s'
    Simple.CatchTerm d1 d2 t1 ->
      let h' d3 =
            createKClosure k $ \ d6 ->
              createHClosure h $ \ d7 -> do
                c1s <- getStandardRules
                i   <- getNormalResultIndex undefined
                c   <- do d4 <- gen
                          d5 <- gen
                          return ([d4], CPS.ConstructorTerm d5 d2 0 [d4]
                                      $ CPS.ApplyTerm d6 [d5, d7])
                c1s <- return $ substitute i c c1s
                i   <- getThrowIndex d1
                c   <- do d4 <- gen
                          d5 <- gen
                          return ([d4, d5], CPS.ConstructorTerm d6 d2 1 [d4, d5]
                                          $ CPS.ApplyTerm d6 [d6, d7])
                c1s <- return $ substitute i c c1s
                return $ CPS.CaseTerm d3 c1s
          k' h d3 = do
            d4  <- gen
            d5  <- getResultTypeIdent
            i   <- getNormalResultIndex undefined
            t2' <- h d4
            return $ CPS.ConstructorTerm d4 d5 i [d3] t2'
       in convertTerm t1 h' k'
    -- Should we do something to make this better?
    Simple.FunTerm d1 -> do
      d2  <- gen
      t1' <- k h d2
      d3  <- gen
      d4  <- gen
      d5  <- getResultTypeIdent
      ty1 <- getFunType d1
      ty2s <- return $ [ CPS.ArrowType [ty1, CPS.ArrowType [CPS.SumType d5]]
                       , CPS.ArrowType [CPS.SumType d5]
                       ]
      return $ CPS.LambdaTerm d2 [d3, d4] ty2s (CPS.CallTerm d1 [d3, d4]) $ t1'
    Simple.LambdaTerm d1 ty1 t1 -> do
      d2   <- gen
      d3   <- gen
      d4   <- gen
      t1'  <- convertTerm t1 (createH d4) (createK d3)
      t2'  <- k h d2
      ty1' <- convertType ty1
      -- I am not sure how I want to get this type.
      ty3' <- undefined
      d5   <- getResultTypeIdent
      ty2s <- return $ [ ty1'
                       , CPS.ArrowType [ty3', CPS.ArrowType [CPS.SumType d5]]
                       , CPS.ArrowType [CPS.SumType d5]
                       ]
      return $ CPS.LambdaTerm d2 [d1, d3, d4] ty2s t1' t2'
    Simple.StringTerm s1 -> do
      d1 <- gen
      t1 <- k h d1
      return $ CPS.StringTerm d1 s1 t1
    Simple.ThrowTerm d1 t1 ->
      convertTerm t1 h $ \ h d1 ->
        createKClosure k $ \ d4 -> do
          d2 <- gen
          d3 <- getResultTypeIdent
          i <- getThrowIndex d1
          t2' <- h d2
          return $ CPS.ConstructorTerm d2 d3 i [d1, d4] t2'
    _ -> undefined

{-
 | BindTerm Ident Term Term
 | ConcatenateTerm Term Term
 | ConstructorTerm Ident Index [Term]
 | TupleTerm [Term]
 | UnitTerm
 | UnreachableTerm Type
 | UntupleTerm [Ident] Term Term
 | VariableTerm Ident
-}

convertType :: Simple.Type -> M CPS.Type
convertType = undefined

getFunType :: Simple.Ident -> M CPS.Type
getFunType = undefined

getStandardRules :: M [([CPS.Ident], CPS.Term)]
getStandardRules = undefined

getNormalResultIndex :: CPS.Type -> M CPS.Index
getNormalResultIndex ty = undefined

-- Returns the sum type ident for Result.
getResultTypeIdent :: M CPS.Ident
getResultTypeIdent = undefined

-- Returns the constructor index for the tag.
getThrowIndex :: Simple.Ident -> M CPS.Index
getThrowIndex d = undefined

createH :: CPS.Ident -> H
createH d1 d2 = return $ CPS.ApplyTerm d1 [d2]

createK :: CPS.Ident -> K
createK d1 h d2 =
  createHClosure h $ \ d3 ->
    return $ CPS.ApplyTerm d1 [d2, d3]

convertRule :: H -> K -> ([Simple.Ident], Simple.Term) -> M ([CPS.Ident], CPS.Term)
convertRule h k (d1s, t1) = do
  t1' <- convertTerm t1 h k
  return (d1s, t1')

type M a = [a]

type K = H -> CPS.Ident -> M CPS.Term
type H = CPS.Ident -> M CPS.Term

-- Eta-reduce the K closure if possibe.
createKClosure :: K -> (CPS.Ident -> M CPS.Term) -> M CPS.Term
createKClosure k m = do
  d1 <- gen
  d2 <- gen
  t1 <- k (\ d3 -> return $ CPS.ApplyTerm d2 [d3]) d1
  ty1 <- undefined
  case t1 of
    CPS.ApplyTerm d3 [d4, d5] | d3 /= d4 && d3 /= d5 && d1 == d4 && d2 == d5 ->
      m d3
    _ -> do
      d3 <- gen
      t2 <- m d3
      d4 <- getResultTypeIdent
      return $ CPS.LambdaTerm d3 [d1, d2] [ty1, CPS.ArrowType [CPS.SumType d4]] t1 t2

-- Eta-reduce the H closure if possibe.
createHClosure :: H -> (CPS.Ident -> M CPS.Term) -> M CPS.Term
createHClosure h m = do
  d1 <- gen
  t1 <- h d1
  case t1 of
    CPS.ApplyTerm d2 [d3] | d2 /= d3 && d1 == d3 ->
      m d2
    _ -> do
      d2 <- gen
      t2 <- m d2
      d3 <- getResultTypeIdent
      return $ CPS.LambdaTerm d2 [d1] [CPS.SumType d3] t1 t2

gen :: M CPS.Ident
gen = undefined

substitute :: Int -> a -> [a] -> [a]
substitute 0 x (_:ys) = x:ys
substitute n x (y:ys) = y : substitute (n-1) x ys
substitute n x []     = error "substitute out of bounds"
