module Compiler.Symbol where

import Control.Applicative

newtype M a = M (Int -> (a, Int))

instance Functor M where
  fmap f (M x) = M $ g
    where g d = let (x', d') = x d
                 in (f x', d')

instance Applicative M where
  pure x = M $ \ d -> (x, d)
  M f <*> M x = M g
    where g d = let (f', d') = f d
                    (x', d'') = x d'
                 in (f' x', d'')

instance Monad M where
  return = pure
  M x >>= f = M g
    where g d = let (x', d') = x d
                    (M x'') = f x'
                 in x'' d'

run :: M a -> a
run (M x) = let (x', _) = x 0
             in x'

gen :: M Int
gen = M g
  where g d = (d, d + 1)