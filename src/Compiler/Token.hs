module Compiler.Token where

-- | Line and column in file; starting at (1, 1).
type Position = (Int, Int)

-- | The position at the start of a file.
posStart :: Position
posStart = (1, 1)

-- | Increments the line number, which resets the column to 1.
lineSucc :: Position -> Position
lineSucc (line, col) = (line + 1, 1)

-- | Increments the column number.
colSucc :: Position -> Position
colSucc (line, col) = (line, col + 1)

-- | A lexical token in the source file.
data Token = EqualsToken
           | ColonToken
           | LeftParenToken
           | RightParenToken
           | LeftBracketToken
           | RightBracketToken
           | LowerToken String
           | UpperToken String
           | IntToken Integer
           | CommaToken
           | RightArrowToken
           | UnderbarToken
           | ComposeToken
           | BangToken
  deriving (Eq, Show)
