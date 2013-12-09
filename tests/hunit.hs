{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import           Control.Exception.Base
-- import           Control.Monad
import           Test.Framework
import           Test.Framework.Providers.HUnit
import           Test.Framework.TH
import           Test.HUnit.Base

import           Compiler.Driver
-- import qualified Compiler.Mini                  as Mini
import qualified Compiler.Syntax                as Syntax
import           Compiler.Token
import qualified Compiler.Type                  as Type
import qualified Compiler.TypeChecker           as TypeChecker

import qualified Compiler.Interpreter           as Interpreter
import qualified Compiler.Lambda                as Lambda

tokens =  [(( 2,  1), UpperToken "Main"),
           (( 2,  5), LeftParenToken),
           (( 2,  6), RightParenToken),
           (( 2,  8), ColonToken),
           (( 2, 10), UpperToken "Output"),
           (( 3,  3), UpperToken "Exit")]

syntax = Syntax.Program [Syntax.FunDec (Syntax.Pos "test01.txt" 2 1) "Main" []
                          [Syntax.UnitPat (Syntax.Pos "test01.txt" 2 5)]
                          (Syntax.UpperTyp (Syntax.Pos "test01.txt" 2 10) "Output")
                          (Syntax.UpperTerm (Syntax.Pos "test01.txt" 3 3) [] Type.Unit "Exit")]

{-
syntax2 = Syntax.Program [Syntax.FunDec (Syntax.Pos "test01.txt" 2 1) "Main" []
                           [Syntax.UnitPat (Syntax.Pos "test01.txt" 2 5)]
                           (Syntax.UpperTyp (Syntax.Pos "test01.txt" 2 10) "Output")
                           (Syntax.UpperTerm (Syntax.Pos "test01.txt" 3 3) [] "Exit")]
-}


-- mini = Mini.Program [(0, Mini.Fun [] (Mini.ConstructorTerm [] ]

case_tokenizer =
  (tokens @=?) =<< evaluate =<< (drive $ tokenize "test01.txt")

case_parser = do
  (syntax @=?) =<< evaluate =<< (drive $ parse "test01.txt")

case_typecheck_unit_term = do
  r @=? TypeChecker.typeCheckTerm TypeChecker.gammaEmpty TypeChecker.sigmaEmpty ty t
 where t  = Syntax.UnitTerm (Syntax.Pos "" 0 0)
       ty = Type.Unit
       r  = Right (Type.Unit, TypeChecker.sigmaEmpty)

-- case_typechecker =
--   void $ evaluate =<< (drive $ typeCheck syntax)

-- case_elaborator =
--   (mini @=?) =<< evaluate =<< (drive $ elaborate syntax2)

case_interpreter_unit =
  case Interpreter.eval Lambda.UnitTerm of
    Interpreter.Normal Interpreter.UnitValue -> return ()
    _ -> error "incorrect"

case_interpreter_tuple =
  case Interpreter.eval (Lambda.TupleTerm [Lambda.UnitTerm, Lambda.UnitTerm]) of
    Interpreter.Normal (Interpreter.TupleValue [Interpreter.UnitValue, Interpreter.UnitValue]) -> return ()
    _ -> error "incorrect"

case_interpreter_variable = check1 $ Interpreter.eval (Lambda.VariableTerm 5)
  where check1 (Interpreter.GetValueEnvironment k) = check2 $ k [(5, Interpreter.UnitValue)]
        check1 _ = error "incorrect"
        check2 (Interpreter.Normal Interpreter.UnitValue) = return ()
        check2 _ = error "incorrect"

program :: Lambda.Program
program = Lambda.Program [] [] [(0, Lambda.Function [] undefined (Lambda.LambdaTerm 0 Lambda.UnitType (Lambda.ConstructorTerm 0 [] 0 [])))] 0

case_interpreter_main = check $ Interpreter.interpret program
  where check Interpreter.ExitStatus = return ()
        check _ = error "incorrect"

case_interpreter_apply = check $ Interpreter.evalClosed t
  where t = Lambda.ApplyTerm (Lambda.LambdaTerm 0 Lambda.UnitType (Lambda.VariableTerm 0)) Lambda.UnitTerm
        check (Interpreter.Normal Interpreter.UnitValue) = return ()
        check _ = error "incorrect"

case_interpreter_bind = check $ Interpreter.evalClosed t
  where t = Lambda.BindTerm 0 Lambda.UnitTerm (Lambda.VariableTerm 0)
        check (Interpreter.Normal Interpreter.UnitValue) = return ()
        check _ = error "incorrect"

case_interpreter_eq = check $ Interpreter.eval t
  where t = Lambda.IsEqualTerm Lambda.UnitType Lambda.UnitTerm Lambda.UnitTerm
        check (Interpreter.Normal (Interpreter.VariantValue 0 [])) = return ()
        check _ = error "incorrect"

case_interpreter_protect_basic = check $ Interpreter.eval t
  where t = Lambda.ProtectTerm (Lambda.StringTerm "a") (Lambda.StringTerm "b")
        check (Interpreter.Normal (Interpreter.StringValue "a")) = return ()
        check _ = error "incorrect"

case_interpreter_case = check $ Interpreter.evalClosed t
  where t = Lambda.CaseTerm (Lambda.ConstructorTerm undefined undefined 1 [])
              [([], Lambda.StringTerm "a"),
               ([], Lambda.StringTerm "b")]
        check (Interpreter.Normal (Interpreter.StringValue "b")) = return ()
        check x = error $ "incorrect: " ++ show x

case_interpreter_show_variant = check1 $ Interpreter.eval t
  where t = Lambda.ShowTerm (Lambda.VariantType 0 []) (Lambda.ConstructorTerm undefined undefined 0 [])
        check1 (Interpreter.LookupVariant 0 k) = check2 $ k $ Lambda.Variant [] ["True", "False"] [[], []]
        check1 _ = error "incorrect 1"
        check2 (Interpreter.Normal (Interpreter.StringValue "True")) = return ()
        check2 _ = error "incorrect 2"

case_interpreter_tag = check $ Interpreter.eval t
  where t = Lambda.TagTerm 5
        check (Interpreter.Normal (Interpreter.TagValue 5)) = return ()
        check _ = error "incorrect"

case_interpreter_throw = check $ Interpreter.eval t
  where t = Lambda.ThrowTerm (Lambda.TagTerm 0) Lambda.UnitTerm
        check (Interpreter.Escape 0 Interpreter.UnitValue _) = return ()
        check _ = error "incorrect"

case_interpreter_catch = check $ Interpreter.eval t
  where t = Lambda.CatchTerm (Lambda.TagTerm 0) 1 (Lambda.StringTerm "b") (Lambda.StringTerm "a")
        check (Interpreter.Normal (Interpreter.StringValue "a")) = return ()
        check _ = error "incorrect"

case_interpreter_catch2 = check $ Interpreter.evalClosed t
  where t = Lambda.CatchTerm (Lambda.TagTerm 0) 1 (Lambda.StringTerm "b")
              (Lambda.ThrowTerm (Lambda.TagTerm 0) (Lambda.StringTerm "a"))
        check (Interpreter.Normal (Interpreter.StringValue "b")) = return ()
        check x = error $ show x

main :: IO ()
main = defaultMain [$testGroupGenerator]
