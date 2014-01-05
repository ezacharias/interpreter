module Compiler.TokenParser
  ( TokenParser (..)
  , tokenParser
  ) where

import           Control.Applicative (Alternative, Applicative, empty, many,
                                      pure, some, (<*>), (<|>))
import           Control.Monad
import           Data.Foldable       (asum)

import qualified Compiler.Syntax     as Syntax
import           Compiler.Token
import qualified Compiler.Type       as Type

-- | A token parser is a data structure which is incrementally fed tokens and returns the result.
data TokenParser a = TokenParserFinished a
                   -- | Passed Nothing if at EOF.
                   | TokenParserTokenRequest ((String, Position, Maybe Token) -> TokenParser a)
                   | TokenParserError Position String

tokenParser :: TokenParser Syntax.Program
tokenParser = runAmbiguousParser ambiguousParser (\ x _ _ _ -> TokenParserFinished x) 0 Nothing emptyEnv

newtype Env = Env { envVal :: [String] }

emptyEnv :: Env
emptyEnv = Env []

envWith :: Env -> [String] -> Env
envWith (Env ss1) ss2 = Env (ss2 ++ ss1)

patLocals :: Syntax.Pat -> [String]
patLocals (Syntax.AscribePat _ p _)    = patLocals p
patLocals (Syntax.LowerPat _ s)        = [s]
patLocals (Syntax.TuplePat _ _ ps)     = concat (map patLocals ps)
patLocals Syntax.UnderbarPat           = []
patLocals (Syntax.UnitPat _)           = []
patLocals (Syntax.UpperPat _ _ _ _ ps) = concat (map patLocals ps)

withPatLocals :: Syntax.Pat -> AmbiguousParser a -> AmbiguousParser a
withPatLocals pat p = do
  let ss = patLocals pat
  r <- localEnv
  withLocalEnv (envWith r ss) p

withPatsLocals :: [Syntax.Pat] -> AmbiguousParser a -> AmbiguousParser a
withPatsLocals pats p = do
  let ss = concat (map patLocals pats)
  r <- localEnv
  withLocalEnv (envWith r ss) p


-- The continuation takes a line and a possible column.

-- | An ambiguous parser takes a continuation, but may call the continuation multiple times with different results.
newtype AmbiguousParser a = AmbiguousParser ((a -> AmbiguousParserContinuation) -> AmbiguousParserContinuation)

type AmbiguousParserContinuation = Int -> Maybe Int -> Env -> TokenParser Syntax.Program

instance Monad AmbiguousParser where
  return x = AmbiguousParser (\ k -> k x)
  AmbiguousParser g >>= f = AmbiguousParser check
    where check k = g (\ x -> runAmbiguousParser (f x) k)

instance Functor AmbiguousParser where
  fmap f (AmbiguousParser g) = AmbiguousParser (\ k -> g (k . f))

instance Applicative AmbiguousParser where
  pure x = AmbiguousParser (\ k -> k x)
  AmbiguousParser f <*> AmbiguousParser x = AmbiguousParser (\ k -> f (\ f' -> x (k . f')))

instance Alternative AmbiguousParser where
  empty = failure
  (<|>) = alt

runAmbiguousParser :: AmbiguousParser a -> (a -> AmbiguousParserContinuation) -> AmbiguousParserContinuation
runAmbiguousParser (AmbiguousParser f) = f

failurePosMsg :: Syntax.Pos -> String -> AmbiguousParser a
failurePosMsg (Syntax.Pos _ line col) msg = AmbiguousParser (\ _ _ _ _ -> TokenParserError (line, col) msg)

failurePos :: Syntax.Pos -> AmbiguousParser a
failurePos pos = failurePosMsg pos ""

failure :: AmbiguousParser a
failure = failurePos =<< position

alt :: AmbiguousParser a -> AmbiguousParser a -> AmbiguousParser a
alt p1 p2 = AmbiguousParser (\ k l c r -> check (runAmbiguousParser p1 k l c r) (runAmbiguousParser p2 k l c r))
  where check (TokenParserFinished _)      (TokenParserFinished _)      = error "Compiler.TokenParser.alt: ambiguous syntax"
        check (TokenParserFinished _)      (TokenParserTokenRequest _)  = error "Compiler.TokenParser.alt: impossible"
        check (TokenParserFinished x)      (TokenParserError _ _)       = TokenParserFinished x
        check (TokenParserTokenRequest _)  (TokenParserFinished _)      = error "Compiler.TokenParser.alt: impossible"
        check (TokenParserTokenRequest k1) (TokenParserTokenRequest k2) = TokenParserTokenRequest (\ x -> check (k1 x) (k2 x))
        check (TokenParserTokenRequest k)  (TokenParserError _ _)       = TokenParserTokenRequest k
        check (TokenParserError pos msg)   (TokenParserFinished x)      = TokenParserFinished x
        check (TokenParserError pos msg)   (TokenParserTokenRequest k)  = TokenParserTokenRequest k
        check (TokenParserError pos1 msg1) (TokenParserError pos2 "")   = TokenParserError pos2 msg1
        check (TokenParserError pos1 msg1) (TokenParserError pos2 msg2) = TokenParserError pos2 msg2

choice :: [AmbiguousParser a] -> AmbiguousParser a
choice = asum

-- | The first token matched must be at the given column number.
indented :: Int -> AmbiguousParser a -> AmbiguousParser a
indented n p = do Syntax.Pos _ l1 _ <- position
                  AmbiguousParser (check l1)
  where check l1 k l2 Nothing              = runAmbiguousParser p (\ x _ _ -> k x l2 Nothing) l1 (Just n)
        check l1 k l2 (Just c) | n == c    = runAmbiguousParser p (\ x _ c -> k x l2 c) l1 (Just n)
        check l1 k l2 (Just c) | otherwise = error "Improperly nested indentation requirements."

ambiguousParser :: AmbiguousParser Syntax.Program
ambiguousParser = program

token :: AmbiguousParser Token
token = AmbiguousParser check
  where check k l c r = TokenParserTokenRequest (response k l c r)
        response k _ _ _ (filename, (l2, c2), Nothing) = TokenParserError (l2, c2) ""
        response k l1 Nothing r (filename, (l2, c2), Just tok)
          | l1 == l2 = k tok l2 Nothing r
          | otherwise = TokenParserError (l2, c2) ""
        response k l1 (Just c1) r (filename, (l2, c2), Just tok)
          | l1 == l2 && c1 == c2  = k tok l2 Nothing r
          | otherwise = TokenParserError (l2, c2) ""

position :: AmbiguousParser Syntax.Pos
position = AmbiguousParser check
  where check k l c r = TokenParserTokenRequest (response k l c r)
        response k l c r x@(filename, (line, col), _) = test x (k (Syntax.Pos filename line col) l c r)
        test x (TokenParserTokenRequest k) = k x
        test _ (TokenParserFinished x) = error "Compiler.TokenParser.position: impossible"
        test x (TokenParserError pos msg) = TokenParserError pos msg

localEnv :: AmbiguousParser Env
localEnv = AmbiguousParser f
  where f k l c r = k r l c r

withLocalEnv :: Env -> AmbiguousParser a -> AmbiguousParser a
withLocalEnv r1 p = AmbiguousParser f
  where f k l c r2 = runAmbiguousParser p (g k r2) l c r1
        g k r2 x l c _ = k x l c r2

isToken :: Token -> AmbiguousParser ()
isToken tok1 = do
  pos <- position
  tok2 <- token
  unless (tok1 == tok2) $ failurePos pos

eof :: AmbiguousParser ()
eof = AmbiguousParser check
  where check k l c r = TokenParserTokenRequest (response k l c r)
        response k l c r (filename, pos, Nothing)  = k () l c r
        response k l c r (filename, pos, Just tok) = TokenParserError pos ""

topLevelIndentation :: Int
topLevelIndentation = 4

program :: AmbiguousParser Syntax.Program
program = do
  xs <- many (indented (1 + topLevelIndentation) dec)
  eof
  return $ Syntax.Program xs

dec :: AmbiguousParser Syntax.Dec
dec = funDec <|> sumDec <|> newDec <|> unitDec <|> modDec

upper :: AmbiguousParser String
upper = do
  pos <- position
  t <- token
  case t of
    UpperToken x -> return x
    _ -> failurePos pos

dotUpper :: AmbiguousParser String
dotUpper = do
  pos <- position
  t <- token
  case t of
    DotUpperToken x -> return x
    _ -> failurePos pos

qual :: AmbiguousParser Syntax.Qual
qual = do x <- upper
          xs <- many dotUpper
          return $ x:xs

leftBracket :: AmbiguousParser ()
leftBracket = isToken LeftBracketToken

lower :: AmbiguousParser String
lower = do
  pos <- position
  t <- token
  case t of
    LowerToken x -> return x
    _ -> failurePos pos


string :: AmbiguousParser String
string = do
  pos <- position
  t <- token
  case t of
    StringToken x -> return x
    _ -> failurePos pos

comma :: AmbiguousParser ()
comma = isToken CommaToken

colon :: AmbiguousParser ()
colon = isToken ColonToken

equals :: AmbiguousParser ()
equals = isToken EqualsToken

rightArrow :: AmbiguousParser ()
rightArrow = isToken RightArrowToken

leftParen :: AmbiguousParser ()
leftParen = isToken LeftParenToken

rightParen :: AmbiguousParser ()
rightParen = isToken RightParenToken

rightBracket :: AmbiguousParser ()
rightBracket = isToken RightBracketToken

-- Keywords can be shadowed by local variable bindings.

keyword :: String -> AmbiguousParser ()
keyword s1 = do
  pos <- position
  r <- localEnv
  x <- token
  case x of
    LowerToken s2 | s1 == s2 && not (elem s1 (envVal r)) -> return ()
    _ -> failurePos pos

funDec :: AmbiguousParser Syntax.Dec
funDec = do
  pos@(Syntax.Pos _ _ c) <- position
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
  e5 <- withPatsLocals e3 $
          indented (c + 2) stm0
  return $ Syntax.FunDec pos e1 e2 e3 e4 e5

stm0 :: AmbiguousParser Syntax.Term
stm0 = bindStm <|> seqStm <|> stm1

bindStm :: AmbiguousParser Syntax.Term
bindStm = do
  Syntax.Pos _ _ c <- position
  keyword "bind"
  p <- pat0
  keyword "to"
  t1 <- stm1
  t2 <- withPatLocals p $ indented c stm0
  return $ Syntax.BindTerm Type.Unit p t1 t2

seqStm :: AmbiguousParser Syntax.Term
seqStm = do
  Syntax.Pos _ _ c <- position
  t1 <- stm1
  indented c $ do
    t2 <- stm0
    return $ Syntax.SeqTerm t1 t2

stm1 :: AmbiguousParser Syntax.Term
stm1 = caseStm <|> term0

caseStm :: AmbiguousParser Syntax.Term
caseStm = do
  Syntax.Pos _ _ c <- position
  keyword "case"
  t <- term2
  rs <- some $ indented (c + 2) rule
  return $ Syntax.CaseTerm Type.Unit t rs

rule :: AmbiguousParser (Syntax.Pat, Syntax.Term)
rule = do
  Syntax.Pos _ _ c <- position
  p <- pat0
  t <- withPatLocals p $ indented (c + 2) stm0
  return (p, t)

term0 :: AmbiguousParser Syntax.Term
term0 = do
  e <- term2
  choice [ ascribeTerm e
         , return e
         ]

ascribeTerm :: Syntax.Term -> AmbiguousParser Syntax.Term
ascribeTerm t = do
  pos <- position
  colon
  ty <- typ0
  return $ Syntax.AscribeTerm pos t ty

term1 :: AmbiguousParser Syntax.Term
term1 = term2

term2 :: AmbiguousParser Syntax.Term
term2 = do
  e <- exp3
  choice [ applyTerm e
         , return e
         ]

applyTerm :: Syntax.Term -> AmbiguousParser Syntax.Term
applyTerm t1 = do
  t2 <- exp4
  choice [ applyTerm (Syntax.ApplyTerm Type.Unit t1 t2)
         , return (Syntax.ApplyTerm Type.Unit t1 t2)
         ]

exp3 :: AmbiguousParser Syntax.Term
exp3 = choice [ do pos <- position
                   x <- lower
                   r <- localEnv
                   if elem x (envVal r) then
                     return $ Syntax.VariableTerm pos x
                   else
                     failurePosMsg pos $ "Unbound variable " ++ x ++ "."
              , do pos <- position
                   x <- qual
                   return $ Syntax.UpperTerm pos [] Type.Unit x
              , do pos <- position
                   x <- string
                   return $ Syntax.StringTerm pos x
              , exp4
              ]

exp4 :: AmbiguousParser Syntax.Term
exp4 = do
  choice [ do pos <- position
              leftParen
              rightParen
              return $ Syntax.UnitTerm pos
         , do leftParen
              e <- term0
              rightParen
              return e
         , do pos <- position
              leftParen
              t <- term0
              ts <- some $ comma >> term0
              rightParen
              return $ Syntax.TupleTerm pos (map (\ _ -> Type.Unit) (t:ts)) (t:ts)
         ]

pat0 :: AmbiguousParser Syntax.Pat
pat0 = do
  p <- pat1
  choice [ do pos <- position
              colon
              ty <- typ0
              return $ Syntax.AscribePat pos p ty
         , return p
         ]

pat1 :: AmbiguousParser Syntax.Pat
pat1 =
  choice [ upperPat
         , pat2
         ]

upperPat :: AmbiguousParser Syntax.Pat
upperPat = do
  pos <- position
  s <- qual
  ps <- many pat3
  return $ Syntax.UpperPat pos [] Type.Unit s ps

pat2 :: AmbiguousParser Syntax.Pat
pat2 =
  choice [ do t <- token
              case t of
                UnderbarToken -> return Syntax.UnderbarPat
                _ -> failure
         , do pos <- position
              x <- lower
              return $ Syntax.LowerPat pos x
         , pat3
         ]

pat3 :: AmbiguousParser Syntax.Pat
pat3 =
  choice [ do pos <- position
              leftParen
              rightParen
              return $ Syntax.UnitPat pos
         , do pos <- position
              leftParen
              p <- pat0
              ps <- some $ comma >> pat0
              rightParen
              return $ Syntax.TuplePat pos (map (\ _ -> Type.Unit) (p:ps)) (p:ps)
         , do leftParen
              p <- pat0
              rightParen
              return p
         ]

typ0 :: AmbiguousParser Syntax.Typ
typ0 = do
  ty <- typ1
  tys <- many $ rightArrow >> typ1
  return $ foldl Syntax.ArrowTyp ty tys

typ1 :: AmbiguousParser Syntax.Typ
typ1 = do
  choice [ lowerTyp
         , upperTyp
         , typ2
         ]

typ2 :: AmbiguousParser Syntax.Typ
typ2 = do
  choice [ tupleTyp
         , unitTyp
         , do leftParen
              ty <- typ0
              rightParen
              return ty
         ]

lowerTyp :: AmbiguousParser Syntax.Typ
lowerTyp = liftM Syntax.LowerTyp lower


tupleTyp :: AmbiguousParser Syntax.Typ
tupleTyp = do
  leftParen
  ty <- typ0
  tys <- some $ comma >> typ0
  rightParen
  return $ Syntax.TupleTyp (ty:tys)

unitTyp :: AmbiguousParser Syntax.Typ
unitTyp = do
  pos <- position
  leftParen
  rightParen
  return $ Syntax.UnitTyp pos

upperTyp :: AmbiguousParser Syntax.Typ
upperTyp = do
  pos <- position
  e1 <- qual
  e2 <- choice [ do leftBracket
                    e2 <- liftM2 (:) typ0 (many $ comma >> typ0)
                    rightBracket
                    return e2
               , return []
               ]
  return $ Syntax.UpperTyp pos e1 e2

undefinedPosition :: Syntax.Pos
undefinedPosition = Syntax.Pos "" 0 0

sumDec :: AmbiguousParser Syntax.Dec
sumDec = do
  pos@(Syntax.Pos _ l c) <- position
  keyword "sum"
  e1 <- upper
  e2 <- choice [ do leftBracket
                    e2 <- liftM2 (:) lower (many $ comma >> lower)
                    rightBracket
                    return e2
               , return []
               ]
  e3 <- many $ indented (c + 2) constructor
  return $ Syntax.SumDec pos e1 e2 e3

constructor :: AmbiguousParser (Syntax.Pos, String, [Syntax.Typ])
constructor = do
  pos <- position
  e1 <- upper
  e2 <- many typ2
  return (pos, e1, e2)

modDec :: AmbiguousParser Syntax.Dec
modDec = do
  pos@(Syntax.Pos _ _ c) <- position
  keyword "mod"
  e1 <- upper
  e2 <- many $ indented (c + 2) dec
  return $ Syntax.ModDec pos e1 e2

newDec :: AmbiguousParser Syntax.Dec
newDec = do
  pos <- position
  keyword "new"
  e1 <- upper
  equals
  e2 <- qual
  e3 <- choice [ do leftBracket
                    e3 <- liftM2 (:) typ0 (many $ comma >> typ0)
                    rightBracket
                    return e3
               , return []
               ]
  return $ Syntax.NewDec pos e1 e2 e3

unitDec :: AmbiguousParser Syntax.Dec
unitDec = do
  pos@(Syntax.Pos _ _ c) <- position
  keyword "unit"
  e1 <- upper
  e2 <- choice [ do leftBracket
                    e3 <- liftM2 (:) lower (many $ comma >> lower)
                    rightBracket
                    return e3
               , return []
               ]
  e3 <- many $ indented (c + 2) dec
  return $ Syntax.UnitDec pos e1 e2 e3
