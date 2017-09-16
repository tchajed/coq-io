module Main where

-- import Prog (countNewlines)
import Prog
import Interpreter
import System.Environment (getArgs)
import System.IO.Error (isDoesNotExistError, catchIOError)
import System.IO (withFile, IOMode(..), openFile, hClose)

doesExist :: FilePath -> IO Bool
doesExist fname =
  catchIOError
  (do
      h <- openFile fname ReadMode
      hClose h
      return True)
  (\e -> if isDoesNotExistError e then return False else ioError e)

wordCount :: FilePath -> IO ()
wordCount fname =
  withFile fname ReadWriteMode $ \h -> do
    numLines <- interpret h countNewlines
    print numLines

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
      exists <- doesExist fname
      if exists
        then wordCount fname
        else error (fname ++ " does not exist")
    _ -> error "Usage: word-count <file name>"
