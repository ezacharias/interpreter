module Compiler.Tokenizer
  ( Tokenizer (..)
  , tokenizer
  ) where

import           Compiler.Token

-- | A tokenizer is a data structure which is incrementally fed characters and incrementally returns tokens.
data Tokenizer = TokenizerEndOfFile Position
               | TokenizerToken Position Token Tokenizer
               -- | Passed Nothing if at EOF.
               | TokenizerCharRequest (Maybe Char -> Tokenizer)
               | TokenizerError Position

-- | The char will be the next one presented to a char request. This allows for peeking at a char.
present :: Char -> Tokenizer -> Tokenizer
present c t@(TokenizerEndOfFile pos) = t
present c (TokenizerToken pos tok t) = TokenizerToken pos tok (present c t)
present c (TokenizerCharRequest k)   = k (Just c)
present c t@(TokenizerError pos) = t

tokenizer :: Tokenizer
tokenizer = start posStart

-- A tokenizer for the start of the file, which must check for '\'#!\''.
start :: Position -> Tokenizer
start pos = TokenizerCharRequest check
  where check Nothing = TokenizerEndOfFile pos
        check (Just c) = test c
        test '#'  = startHash (colSucc pos)
        test c    = present c (tok pos)

startHash :: Position -> Tokenizer
startHash pos = TokenizerCharRequest check
  where check Nothing = TokenizerError pos
        check (Just c) = test c
        test '!'  = skipLine (colSucc pos)
        test c = TokenizerError pos

-- The main token matcher.
tok :: Position -> Tokenizer
tok pos = TokenizerCharRequest check
  where check Nothing  = TokenizerEndOfFile pos
        check (Just c) = test c
        test '-'  = dash (colSucc pos)
        test ' '  = tok (colSucc pos)
        test '\n' = tok (lineSucc pos)
        test '='  = TokenizerToken pos EqualsToken (tok (colSucc pos))
        test ':'  = TokenizerToken pos ColonToken (tok (colSucc pos))
        test '('  = TokenizerToken pos LeftParenToken (tok (colSucc pos))
        test ')'  = TokenizerToken pos RightParenToken (tok (colSucc pos))
        test '⟦'  = TokenizerToken pos LeftBracketToken (tok (colSucc pos))
        test '⟧'  = TokenizerToken pos RightBracketToken (tok (colSucc pos))
        test ','  = TokenizerToken pos CommaToken (tok (colSucc pos))
        test '⟶'  = TokenizerToken pos RightArrowToken (tok (colSucc pos))
        test '_'  = TokenizerToken pos UnderbarToken (tok (colSucc pos))
        test '∘'  = TokenizerToken pos ComposeToken (tok (colSucc pos))
        test '!'  = TokenizerToken pos BangToken (tok (colSucc pos))
        test c | '0' <= c && c <= '9'
                  = digit (colSucc pos) pos [c]
        test c | 'a' <= c && c <= 'z'
                  = lower (colSucc pos) pos [c]
        test c | 'A' <= c && c <= 'Z'
                  = upper (colSucc pos) pos [c]
        test _    = TokenizerError pos

dash :: Position -> Tokenizer
dash pos = TokenizerCharRequest check
  where check Nothing = TokenizerError pos
        check (Just c) = test c
        test '-' = skipLine (colSucc pos)
        test _ = TokenizerError pos

skipLine :: Position -> Tokenizer
skipLine pos = TokenizerCharRequest check
  where check Nothing = TokenizerEndOfFile pos
        check (Just c) = test c
        test '\n' = tok (lineSucc pos)
        test _    = skipLine (colSucc pos)

-- In digit, lower, and upper, we pass a reversed string of matched characters to use when matching is complete.
type ReversedString = String

digit :: Position -> Position -> ReversedString -> Tokenizer
digit pos' pos cs = TokenizerCharRequest check
  where check Nothing = TokenizerToken pos (IntToken (read $ reverse cs)) (TokenizerEndOfFile pos)
        check (Just c) = test c
        test c | '0' <= c && c <= '9'
                  = digit (colSucc pos') pos (c:cs)
        test c    = TokenizerToken pos (IntToken (read $ reverse cs)) (present c $ tok pos')

lower :: Position -> Position -> ReversedString -> Tokenizer
lower pos' pos cs = TokenizerCharRequest check
  where check Nothing = TokenizerToken pos (LowerToken (reverse cs)) (TokenizerEndOfFile pos)
        check (Just c) = test c
        test c | 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z'
                  = lower (colSucc pos') pos (c:cs)
        test c    = TokenizerToken pos (LowerToken (reverse cs)) (present c $ tok pos')

upper :: Position -> Position -> ReversedString -> Tokenizer
upper pos' pos cs = TokenizerCharRequest check
  where check Nothing = TokenizerToken pos (UpperToken (reverse cs)) (TokenizerEndOfFile pos)
        check (Just c) = test c
        test c | 'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '.'
                  = upper (colSucc pos') pos (c:cs)
        test c    = TokenizerToken pos (UpperToken (reverse cs)) (present c $ tok pos')
