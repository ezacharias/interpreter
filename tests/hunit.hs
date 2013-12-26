{- OPTIONS_GHC -fno-warn-missing-signatures -}
{- LANGUAGE TemplateHaskell -}

module Main where

-- import           Control.Exception.Base
-- import           Control.Monad
import           Test.Framework
import           Test.Framework.Providers.HUnit
import           Test.HUnit.Base                hiding (Test)

import qualified Compiler.Elaborator            as Elaborator
-- import qualified Compiler.Lambda                as Lambda
import qualified Compiler.Syntax                as Syntax

main :: IO ()
main = defaultMain tests

tests :: [Test]
tests =
 [ testCase "empty program names" $
     let v' = Elaborator.runM m k rs v 0
         v = Elaborator.emptyEnv
         rs = [Elaborator.emptyRename]
         k () v _ = v
         m = Elaborator.convertDec (Syntax.ModDec undefined "M" [])
      in v' @?= Elaborator.Env [] [] [] []
{-
 , testCase "single tag" $
     let v' = Elaborator.runM m k rs v 0
         v = Elaborator.emptyEnv
         rs = [Elaborator.Rename [] [] [("T", 7)] []]
         k () v _ = v
         m = Elaborator.convertDec (Syntax.TagDec undefined "T" undefined)
      in v' @?= Elaborator.Env [] [(7, Lambda.Tag Lambda.UnitType Lambda.UnitType)] [] []
 , testCase "tag in module" $
     let v' = Elaborator.runM m k rs v 0
         v = Elaborator.emptyEnv
         rs = [Elaborator.Rename [] [("M", Elaborator.Rename [] [] [("T", 7)] [])] [] []]
         k () v _ = v
         m = Elaborator.convertDec (Syntax.ModDec undefined "M" [Syntax.TagDec undefined "T" undefined])
      in v' @?= Elaborator.Env [] [(7, Lambda.Tag Lambda.UnitType Lambda.UnitType)]
 , testCase "tag in unit" $
     let v' = Elaborator.runM m k rs v 0
         v = Elaborator.emptyEnv
         rs = [Elaborator.Rename
                 [("U", 5)]
                 [("M", Elaborator.Rename [] [] [("T", 7)] [])]
                 []
                 []
              ]
         k () v _ = v
         m = mapM_ Elaborator.convertDec
                     [ Syntax.UnitDec (error "a") "U" [] [Syntax.TagDec (Syntax.Pos "" 0 0) "T" (Syntax.UnitTyp (Syntax.Pos "" 0 0))]
                     , Syntax.NewDec (error "d") "M" ["U"] []
                     ]
      in v' @?= Elaborator.Env [] [(7, Lambda.Tag Lambda.UnitType Lambda.UnitType)]
 , testCase "empty name to rename" $
     let x = Elaborator.runM m k [] v 0
         v = Elaborator.emptyEnv
         m = Elaborator.update n
         k x _ _ = x
         n = Elaborator.Name [] [] []
      in x @?= Elaborator.Rename [] [] [] []
-}
 ]
