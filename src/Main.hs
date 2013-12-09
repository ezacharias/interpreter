-- | Main entry point to the application.
module Main (main) where

import           System.Environment

import           Compiler.Driver

main :: IO ()
main = drive . interpreter =<< getFilename

getFilename :: IO String
getFilename = getArgs >>= check
  where check [filename] = return filename
        check _ = error "Incorrect number of arguments."
