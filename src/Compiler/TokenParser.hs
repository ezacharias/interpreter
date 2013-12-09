--------------------------------------------------------------------------------
-- We need to get the filename. We can either pass it in with each token or we
-- can pass it in at the beginning or we can return a function from a filename
-- to syntax.
--
-- What position is EOF? I think we should have a position for EOF so we can
-- report the position when reporting errors.
--------------------------------------------------------------------------------

module Compiler.TokenParser
  ( TokenParser (..)
  , tokenParser
  ) where

import           Control.Monad

import qualified Compiler.Syntax as Syntax
import           Compiler.Token
import qualified Compiler.Type as Type

-- | A token parser is a data structure which is incrementally fed tokens and returns the result.
data TokenParser a = TokenParserFinished a
                   -- | Passed Nothing if at EOF.
                   | TokenParserTokenRequest (Maybe (String, Position, Token) -> TokenParser a)
                   | TokenParserError Position String

instance Monad TokenParser where
  return = TokenParserFinished
  TokenParserFinished x     >>= f = f x
  TokenParserTokenRequest k >>= f = TokenParserTokenRequest (k >=> f)
  TokenParserError pos msg  >>= f = TokenParserError pos msg

tokenParser :: TokenParser Syntax.Program
tokenParser = runAmbiguousParser ambiguousParser TokenParserFinished

-- | An ambiguous parser takes a continuation, but may call the continuation multiple times with different results.
newtype AmbiguousParser a = AmbiguousParser ((a -> TokenParser Syntax.Program) -> TokenParser Syntax.Program)

instance Monad AmbiguousParser where
  return x = AmbiguousParser (\ k -> k x)
  AmbiguousParser g >>= f = AmbiguousParser check
    where check k = g (\ x -> runAmbiguousParser (f x) k)

runAmbiguousParser :: AmbiguousParser a -> (a -> TokenParser Syntax.Program) -> TokenParser Syntax.Program
runAmbiguousParser (AmbiguousParser f) = f

failurePos :: Syntax.Pos -> AmbiguousParser a
failurePos (Syntax.Pos _ line col) = AmbiguousParser (\ k -> TokenParserError (line, col) "Parsing error.")

failure :: AmbiguousParser a
failure = failurePos =<< position

alt :: AmbiguousParser a -> AmbiguousParser a -> AmbiguousParser a
alt p1 p2 = AmbiguousParser (\ k -> check (runAmbiguousParser p1 k) (runAmbiguousParser p2 k))
  where check (TokenParserFinished x)      (TokenParserFinished _)      = TokenParserFinished x
        check (TokenParserFinished x)      (TokenParserTokenRequest _)  = error "Compiler.TokenParser.alt: impossible"
        check (TokenParserFinished x)      (TokenParserError _ _)       = TokenParserFinished x
        check (TokenParserTokenRequest k)  (TokenParserFinished _)      = error "Compiler.TokenParser.alt: impossible"
        check (TokenParserTokenRequest k1) (TokenParserTokenRequest k2) = TokenParserTokenRequest (\ x -> check (k1 x) (k2 x))
        check (TokenParserTokenRequest k)  (TokenParserError _ _)       = TokenParserTokenRequest k
        check (TokenParserError pos msg)   (TokenParserFinished x)      = TokenParserFinished x
        check (TokenParserError pos msg)   (TokenParserTokenRequest k)  = TokenParserTokenRequest k
        check (TokenParserError pos1 msg1) (TokenParserError pos2 msg2) = TokenParserError pos2 msg2

choice :: [AmbiguousParser a] -> AmbiguousParser a
choice = foldr alt failure

many :: AmbiguousParser a -> AmbiguousParser [a]
many p = choice [ liftM2 (:) p (many p)
                , return []
                ]

many1 :: AmbiguousParser a -> AmbiguousParser [a]
many1 p = liftM2 (:) p (many p)

-- | The first token matched must be at the given column number.
aligned :: Int -> AmbiguousParser a -> AmbiguousParser a
aligned col1 p = AmbiguousParser (check . runAmbiguousParser p)
  where check (TokenParserFinished x)     = error "Foo"
        check (TokenParserTokenRequest k) = TokenParserTokenRequest (respond k)
        check (TokenParserError pos msg)  = TokenParserError pos msg
        respond k Nothing = k Nothing
        respond k (Just (filename, (line2, col2), tok))
           | col1 == col2 = k (Just (filename, (line2, col2), tok))
           | otherwise    = TokenParserError (line2, col2) "Not properly aligned"

-- | Every token must sit on the given line number.
line :: Int -> AmbiguousParser a -> AmbiguousParser a
line line1 p = AmbiguousParser (check . runAmbiguousParser p)
  where check (TokenParserFinished x)     = TokenParserFinished x
        check (TokenParserTokenRequest k) = TokenParserTokenRequest (respond k)
        check (TokenParserError pos msg)  = TokenParserError pos msg
        respond k Nothing = k Nothing
        respond k (Just (filename, (line2, col2), tok))
         | line1 == line2 = k (Just (filename, (line2, col2), tok))
         | otherwise      = TokenParserError (line2, col2) "Not on the same line."

ambiguousParser :: AmbiguousParser Syntax.Program
ambiguousParser = program

token :: AmbiguousParser Token
token = AmbiguousParser check
  where check k = TokenParserTokenRequest (response k)
        response k Nothing = TokenParserError (0,0) "Parsing error."
        response k (Just (filename, pos, tok)) = k tok

position :: AmbiguousParser Syntax.Pos
position = AmbiguousParser check
  where check k = TokenParserTokenRequest (response k)
        response k Nothing = TokenParserError (0,0) "Parsing error."
        response k x@(Just (filename, (line, col), tok)) = test x (k (Syntax.Pos filename line col))
        test x (TokenParserTokenRequest k) = k x
        test _ (TokenParserFinished x) = error "Compiler.TokenParser.position: impossible"
        test x (TokenParserError pos msg) = TokenParserError pos msg

isToken :: Token -> AmbiguousParser ()
isToken tok1 = do
  pos <- position
  tok2 <- token
  unless (tok1 == tok2) $ failurePos pos

eof :: AmbiguousParser ()
eof = AmbiguousParser check
  where check k = TokenParserTokenRequest (response k)
        response k Nothing = k ()
        response k (Just (filename, pos, tok)) = TokenParserError pos "Parsing error. Expected end of file."

program :: AmbiguousParser Syntax.Program
program = do
  xs <- many (aligned 1 dec)
  eof
  return $ Syntax.Program xs

dec :: AmbiguousParser Syntax.Dec
dec = choice [ funDec
             , sumDec
             , tagDec
             ]

upper :: AmbiguousParser Syntax.Ident
upper = do
  t <- token
  case t of
    UpperToken x -> return x
    _ -> failure

leftBracket :: AmbiguousParser ()
leftBracket = do
  t <- token
  case t of
    LeftBracketToken -> return ()
    _ -> failure

lower :: AmbiguousParser Syntax.Ident
lower = error "lower"

comma :: AmbiguousParser ()
comma = error "comma"

colon :: AmbiguousParser ()
colon = isToken ColonToken

leftParen :: AmbiguousParser ()
leftParen = isToken LeftParenToken

rightParen :: AmbiguousParser ()
rightParen = isToken RightParenToken

rightBracket :: AmbiguousParser ()
rightBracket = error "right bracket"

funDec :: AmbiguousParser Syntax.Dec
funDec = do
  pos <- position
  e1 <- upper
  e2 <- choice [ do leftBracket
                    e2 <- liftM2 (:) lower (many $ comma >> lower)
                    rightBracket
                    return e2
               , return []
               ]
  e3 <- many pat3
  colon
  e4 <- typ0
  e5 <- withLocals (patsLocals e3) $
          setRequirement 0 stm0
  return $ Syntax.FunDec pos e1 e2 e3 e4 e5

withLocals :: [String] -> AmbiguousParser a -> AmbiguousParser a
withLocals xs p = p

patsLocals :: [Syntax.Pat] -> [String]
patsLocals _ = return []

setRequirement :: Int -> AmbiguousParser a -> AmbiguousParser a
setRequirement n p = p

stm0 :: AmbiguousParser Syntax.Term
stm0 = do
  exp2

exp2 :: AmbiguousParser Syntax.Term
exp2 = do
  e <- exp3
  choice [ applyExp e
         , return e
         ]

applyExp :: Syntax.Term -> AmbiguousParser Syntax.Term
applyExp e1 = do
  e2 <- exp4
  choice [ applyExp (Syntax.ApplyTerm Type.Unit e1 e2)
         , return (Syntax.ApplyTerm Type.Unit e1 e2)
         ]

exp3 :: AmbiguousParser Syntax.Term
exp3 = exp4

exp4 :: AmbiguousParser Syntax.Term
exp4 =
  choice [ do pos <- position
              leftParen
              rightParen
              return $ Syntax.UnitTerm pos
         , do leftParen
              e <- exp2
              rightParen
              return e
         , do  pos <- position
               x <- upper
               return $ Syntax.UpperTerm pos [] Type.Unit x
         ]

pat3 :: AmbiguousParser Syntax.Pat
pat3 = do
  pos <- position
  leftParen
  rightParen
  return $ Syntax.UnitPat pos

typ0 :: AmbiguousParser Syntax.Typ
typ0 = do
  pos <- position
  x <- upper
  return $ Syntax.UpperTyp pos x

undefinedPosition :: Syntax.Pos
undefinedPosition = Syntax.Pos "" 0 0

sumDec :: AmbiguousParser Syntax.Dec
sumDec = undefinedFailure

tagDec :: AmbiguousParser Syntax.Dec
tagDec = undefinedFailure

undefinedFailure :: AmbiguousParser a
undefinedFailure = failure
