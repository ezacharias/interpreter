module Compiler.Parser where

import qualified Compiler.Syntax as Syntax
import           Compiler.Token
import           Compiler.Tokenizer
import           Compiler.TokenParser

data Parser = ParserFinished Syntax.Program
            | ParserCharRequest (Maybe Char -> Parser)
            | ParserError Position String
            | ParserTokenizerError Position

-- The parser is formed from the tokenizer and the tokenParser.

parser :: String -> Parser
parser filename = parse tokenizer tokenParser
  where parse :: Tokenizer -> TokenParser Syntax.Program -> Parser
        parse t (TokenParserFinished prog)  = ParserFinished prog
        parse t (TokenParserTokenRequest k) = tokenize k t
        parse t (TokenParserError pos msg)  = ParserError pos msg
        tokenize :: (Maybe (String, Position, Token) -> TokenParser Syntax.Program) -> Tokenizer -> Parser
        tokenize k t@TokenizerEndOfFile = parse t $ k Nothing
        tokenize k (TokenizerToken pos tok t) = parse t $ k (Just (filename, pos, tok))
        tokenize k (TokenizerCharRequest k2)  = ParserCharRequest (tokenize k . k2)
        tokenize k (TokenizerError pos)       = ParserTokenizerError pos
