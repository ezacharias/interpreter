module Compiler.CPS.Convert where

import Control.Monad (forM)
import Data.Maybe (fromMaybe)

import qualified Compiler.CPS as CPS
import qualified Compiler.Simple as Simple

convertTerm :: Simple.Term -> H -> K -> M CPS.Term
convertTerm t h k =
  case t of
    Simple.ApplyTerm t1 t2 ->
      convertTerm t1 h $ \ h d1 ty1 ->
        convertTerm t2 h $ \ h d2 _ ->
          createKClosure k (arrowTypeResult ty1) $ \ d3 _ ->
            createHClosure h $ \ d4 ->
              return $ CPS.ApplyTerm d1 [d2, d3, d4]
    Simple.BindTerm d1 t2 t3 -> do
      convertTerm t2 h $ \ h d2 ty2 -> do
        bind d1 d2 ty2 $
          convertTerm t3 h k
    Simple.CaseTerm t1 c1s -> do
      convertTerm t1 h $ \ h d1 _ -> do
        ty2 <- undefined -- this should come from the case term
        createKClosure k ty2 $ \ d3 _ ->
          createHClosure h $ \ d4 -> do
            c1s' <- mapM (convertRule (createH d4) (createK d3)) c1s
            return $ CPS.CaseTerm d1 c1s'

    Simple.CatchTerm d1 d2 t1 ->
      -- We have to begin here, which handles the catch. I think it should
      -- very nearly simply call the function with h, k, and the result, which
      -- would be easy.
      let h' d3 = do
            -- The type given to K is the stream type, which I suppose we should calculate using the given types.
            (ty1, ty2) <- undefined
            ty3 <- undefined -- this should be part of catch
            ty4 <- getStreamType ty1 ty2 ty3
            createKClosure k ty4 $ \ d6 _ ->
              createHClosure h $ \ d7 -> do
                d8 <- createHandlerFunction
                return $ CPS.CallTerm d8 [d3, d6, d7]
          k' h d3 ty3 = do
            d4  <- gen
            -- This I think could be a normal result to a particular tag, but
            -- I'm not sure we want to do that.
            d5  <- getResultTypeIdent
            i   <- getNormalResultIndex ty3
            t2' <- h d4
            return $ CPS.ConstructorTerm d4 d5 i [d3]
                   $ t2'
       in convertTerm t1 h' k'

    -- Should we do something to make this better?
    Simple.FunTerm d1 -> do
      d2  <- gen
      ty1 <- getFunType d1
      t1  <- k h d2 ty1
      d3  <- gen
      d4  <- gen
      ty0 <- getHandlerType
      return $ CPS.LambdaTerm d2 [d3, d4] [CPS.ArrowType [ty1, ty0], ty0] (CPS.CallTerm d1 [d3, d4])
             $ t1
    Simple.LambdaTerm d1 ty1 t1 -> do
      d1' <- gen
      ty1' <- convertType ty1
      bind d1 d1' ty1' $ do
        d2   <- gen
        d3   <- gen
        d4   <- gen
        t1'  <- convertTerm t1 (createH d4) (createK d3)
        ty2' <- undefined -- should be in the lambda
        ty0' <- getHandlerType
        t2'  <- k h d2 (CPS.ArrowType [ty1', CPS.ArrowType [ty2', ty0'], ty0'])
        return $ CPS.LambdaTerm d2 [d1', d3, d4] [ty1', CPS.ArrowType [ty2', ty0'], ty0'] t1' t2'
    Simple.StringTerm s1 -> do
      d1 <- gen
      t1 <- k h d1 CPS.StringType
      return $ CPS.StringTerm d1 s1 t1
    Simple.ThrowTerm d1 t1 ->
      convertTerm t1 h $ \ h d1 ty1 -> do
        ty2 <- getTagResultType d1
        createKClosure k ty2 $ \ d2 _ -> do
          d3 <- gen
          d4 <- getResultTypeIdent
          i <- getThrowIndex d1
          t2 <- h d3
          return $ CPS.ConstructorTerm d3 d4 i [d1, d2]
                 $ t2
    Simple.UnreachableTerm _ -> do
      -- This should not take a type.
      return $ CPS.UnreachableTerm
    Simple.VariableTerm d1 -> do
      (d2, ty2) <- lookupIdent d1
      k h d2 ty2
    _ -> undefined

{-
 | ConcatenateTerm Term Term
 | ConstructorTerm Ident Index [Term]
 | TupleTerm [Term]
 | UnitTerm
 | UntupleTerm [Ident] Term Term
-}

convertType :: Simple.Type -> M CPS.Type
convertType ty =
  case ty of
    Simple.ArrowType ty1 ty2 -> do
      ty0' <- getHandlerType
      ty1' <- convertType ty1
      ty2' <- convertType ty2
      return $ CPS.ArrowType [ty1', CPS.ArrowType [ty2', ty0'], ty0']
    Simple.StringType ->
      return $ CPS.StringType
    Simple.TupleType tys -> do
      tys' <- mapM convertType tys
      return $ CPS.TupleType tys'
    Simple.UnitType ->
      return $ CPS.TupleType []
    Simple.SumType s1 ->
      return $ CPS.SumType s1

getHandlerType :: M CPS.Type
getHandlerType = do
  d <- getResultTypeIdent
  return $ CPS.ArrowType [CPS.SumType d]

createH :: CPS.Ident -> H
createH d1 d2 = return $ CPS.ApplyTerm d1 [d2]

createK :: CPS.Ident -> K
createK d1 h d2 _ =
  createHClosure h $ \ d3 ->
    return $ CPS.ApplyTerm d1 [d2, d3]

convertRule :: H -> K -> ([Simple.Ident], Simple.Term) -> M ([CPS.Ident], CPS.Term)
convertRule h k (d1s, t1) = do
  t1' <- convertTerm t1 h k
  return (d1s, t1')

-- Eta-reduce the K closure if possibe.
createKClosure :: K -> CPS.Type -> (CPS.Ident -> CPS.Type -> M CPS.Term) -> M CPS.Term
createKClosure k ty1 m = do
  d1 <- gen
  d2 <- gen
  t1 <- k (\ d3 -> return $ CPS.ApplyTerm d2 [d3]) d1 ty1
  ty2 <- getHandlerType
  case t1 of
    CPS.ApplyTerm d3 [d4, d5] | d3 /= d4 && d3 /= d5 && d1 == d4 && d2 == d5 ->
      m d3 (CPS.ArrowType [ty1, ty2])
    _ -> do
      d3 <- gen
      t2 <- m d3 (CPS.ArrowType [ty1, ty2])
      return $ CPS.LambdaTerm d3 [d1, d2] [ty1, ty2] t1 t2

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

arrowTypeResult :: CPS.Type -> CPS.Type
arrowTypeResult (CPS.ArrowType [_, CPS.ArrowType [ty, _], _]) = ty
arrowTypeResult _ = error "arrowTypeResult"

type K = H -> CPS.Ident -> CPS.Type -> M CPS.Term
type H = CPS.Ident -> M CPS.Term

newtype M' b a = M { runM :: State -> Reader -> (a -> State -> b) -> b }

type M a = M' CPS.Program a

instance Monad (M' b) where
  return x = M $ \ s _ k -> k x s
  m >>= f = M $ \ s r k -> runM m s r $ \ x s -> runM (f x) s r k

data Reader = R { resultIdent :: CPS.Ident
                , localBindings :: [(Simple.Ident, (CPS.Ident, CPS.Type))]
                }

data State = S { genInt :: Int
               }

look :: (Reader -> a) -> M a
look f = M $ \ s r k -> k (f r) s

with :: (Reader -> Reader) -> M a -> M a
with f m = M $ \ s r k -> runM m s (f r) k

get :: (State -> a) -> M a
get f = M $ \ s _ k -> k (f s) s

set :: (State -> State) -> M ()
set f = M $ \ s _ k -> k () (f s)

-- Generates a new ident.
gen :: M CPS.Ident
gen = do
  i <- get genInt
  set (\ s -> s {genInt = i + 1})
  return i

-- Returns the sum type ident for Result.
getResultTypeIdent :: M CPS.Ident
getResultTypeIdent = do
  look resultIdent

bind :: Simple.Ident -> CPS.Ident -> CPS.Type -> M a -> M a
bind d1 d2 ty2 = with (\ r -> r {localBindings = (d1, (d2, ty2)) : localBindings r})

lookupIdent :: Simple.Ident -> M (CPS.Ident, CPS.Type)
lookupIdent d = do
  xs <- look localBindings
  return $ fromMaybe (undefined) $ lookup d xs


-- Returns the constructor index for the tag.
getThrowIndex :: Simple.Ident -> M CPS.Index
getThrowIndex d = undefined

getFunType :: Simple.Ident -> M CPS.Type
getFunType = undefined

-- The first set is every possible normal result type. The second set is every
-- possible tag result.
getStandardRules :: M [([CPS.Ident], CPS.Term)]
getStandardRules = undefined

getNormalResultIndex :: CPS.Type -> M CPS.Index
getNormalResultIndex ty = undefined

getTagResultType :: CPS.Ident -> M CPS.Type
getTagResultType d = undefined

getStreamType :: CPS.Type -> CPS.Type -> CPS.Type -> M CPS.Type
getStreamType = undefined

makeNormalResult :: CPS.Type -> H -> K -> M ([CPS.Ident], CPS.Term)
makeNormalResult ty1 h k = do
  d1 <- gen
  return ([d1], CPS.UnreachableTerm)

makeTagResult :: CPS.Ident -> CPS.Type -> CPS.Ident -> CPS.Ident -> M ([CPS.Ident], CPS.Term)
makeTagResult fd ty1 hd kd = do
  d1 <- gen
  d2 <- gen
  d3 <- gen
  d4 <- gen
  d5 <- gen
  d6 <- gen
  d7 <- gen
  d8 <- gen
  i  <- gen
  return ( [d1, d2]
         , CPS.LambdaTerm d3 [d4, d5] [ty1, undefined]
             ( CPS.LambdaTerm d6 [d7, d8] [undefined, undefined]
                 ( CPS.CallTerm fd [d7, kd, d8] )
             $ CPS.ApplyTerm d2 [d4, d6]
             )
         $ CPS.ConstructorTerm d7 d8 i [d1, d3]
         $ CPS.ApplyTerm hd [d7]
         )

exportRecursiveFoo :: CPS.Ident -> CPS.Ident -> CPS.Ident -> M CPS.Ident
exportRecursiveFoo d1 kd hd = do
  d0 <- gen
  exportFun d0 $ CPS.Fun [d1, kd, hd] [] $
                   undefined
  undefined


createHandlerFunction :: M CPS.Ident
createHandlerFunction = do
  d0 <- gen
  d1 <- gen
  d2 <- gen
  d3 <- gen
  d4 <- gen
  c1s <- createRules d0 undefined undefined undefined undefined
  exportFun d0 $ CPS.Fun [d1, d2, d3] []
               $   CPS.CaseTerm d4 c1s
  return d0

-- A throw picks an index based only on the tag.
-- d0 is the function to call
-- d1 is the tag
-- ty1 is the result type
createRules :: CPS.Ident -> CPS.Ident -> CPS.Ident -> CPS.Ident -> CPS.Ident -> M [([CPS.Ident], CPS.Term)]
createRules d0 d1 ty1 kd hd = do
  xs <- getTagTypes
  xs' <- forM xs $ \ (d2, ty2, ty3) ->
           if d1 == d2
             then do
               d3 <- gen
               d4 <- gen
               d5 <- gen
               d6 <- gen
               d7 <- gen
               d8 <- gen
               d9 <- gen
               d10 <- gen
               d11 <- gen
               return ( [d3, d4]
                      , CPS.LambdaTerm d5 [d6, d7, d8] []
                          (CPS.LambdaTerm d9 [d10] []
                             (CPS.CallTerm d0 [d10, d7, d8])
                          $ CPS.ApplyTerm d4 [d6, d9]
                          )
                      $ CPS.ConstructorTerm d11 undefined undefined [d3, d5]
                      $ CPS.ApplyTerm kd [d11, hd]
                      )
             else do
               d3 <- gen
               d4 <- gen
               d5 <- gen
               d6 <- gen
               d7 <- gen
               d8 <- gen
               d9 <- gen
               d10 <- gen
               return ( [d3, d4]
                      , CPS.LambdaTerm d5 [d6, d7] []
                          ( CPS.LambdaTerm d8 [d9] []
                              (CPS.CallTerm d0 [d9, kd, d7])
                          $ CPS.ApplyTerm d4 [d6, d8]
                          )
                      $ CPS.ConstructorTerm d10 undefined undefined [d3, d5]
                      $ CPS.ApplyTerm hd [d10]
                      )
  ys <- getNormalTypes
  ys' <- forM ys $ \ ty2 ->
           if ty1 == ty1
             then do
               d3 <- gen
               d4 <- gen
               return ( [d3]
                      , CPS.ConstructorTerm d4 undefined undefined [d3]
                      $ CPS.ApplyTerm kd [d4, hd]
                      )
             else do
               d3 <- gen
               return ( [d3]
                      , CPS.UnreachableTerm
                      )
  return $ xs' ++ ys'


getTagTypes :: M [(CPS.Ident, CPS.Type, CPS.Type)]
getTagTypes = undefined

getNormalTypes :: M [CPS.Type]
getNormalTypes = undefined


{-
            -- The type given to K is the stream type, which I suppose we should calculate using the given types.
            (ty1, ty2) <- undefined
            ty3 <- undefined -- this should be part of catch
            ty4 <- getStreamType ty1 ty2 ty3
            createKClosure k ty4 $ \ d6 _ ->
              createHClosure h $ \ d7 -> do
                c1s <- getStandardRules
                i   <- getNormalResultIndex ty3
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
-}



exportFun :: CPS.Ident -> CPS.Fun -> M ()
exportFun = undefined




-- Utility Functions

substitute :: Int -> a -> [a] -> [a]
substitute 0 x (_ : ys) = x : ys
substitute n x (y : ys) = y : substitute (n-1) x ys
substitute n x []       = error "substitute out of bounds"
