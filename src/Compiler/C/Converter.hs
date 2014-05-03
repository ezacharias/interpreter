module Compiler.C.Converter where

import Compiler.Direct

type M a = [a]

genMain :: M ()
genMain = do
  out "void main() {"
  indent $ do
    out "s->f = f0;"
    out "for (;;)"
    indent $ do
      out "s->f(s);"
    out "return EXIT_SUCCESS;"
  out "}"

genFinished :: M ()
genFinished = do
  out "void finished(struct state *s) {"
  indent $ do
    out "exit(EXIT_SUCCESS);"
  out "}"

genGC :: M ()
genGC = do
  out "void gc(struct state *s) {"
  indent $ do
    out "err(EXIT_FAILURE, \"Out of memory.\");"
  out "}"

genFun :: (Ident, Fun) -> M ()
genFun (d, Fun ds tys t) = do
  s <- getFunName d
  n <- allocationAmount t
  out $ "void " ++ s ++ "(struct state *s) {"
  indent $ do
    out $ "uintptr_t frontier = s->frontier;"
    out $ "if (frontier + " ++ show n ++ " > s->limit) {"
    indent $ do
      out $ "s->gc;"
      out $ "return;"
    out $ "}"
    -- Load the arguments.

    genTerm t
  out $ "}"
  return ()

genTerm :: Term -> M ()
genTerm = undefined

allocationAmount :: Term -> M Int
allocationAmount = undefined

getFunName :: Ident -> M String
getFunName = undefined

out :: String -> M ()
out = undefined

indent :: M () -> M ()
indent = undefined
