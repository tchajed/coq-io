module Interpreter
  ( interpret
  ) where

import Prog
import System.IO

fileInterpret :: Handle -> FileOp a -> IO a
fileInterpret h (Read a) = do
  hSeek h AbsoluteSeek a
  c <- hGetChar h
  return $ unsafeCoerce c
fileInterpret h (Write a v) = do
  hSeek h AbsoluteSeek a
  hPutChar h v
  return $ unsafeCoerce ()
fileInterpret h FileSize = do
  len <- hFileSize h
  return $ unsafeCoerce (len :: Integer)

interpret :: Handle -> FileProg a -> IO a
interpret _ (Ret a) = return a
interpret h (Bind p p') = do
  r <- interpret h p
  interpret h (p' r)
interpret h (Call op) = unsafeCoerce <$> fileInterpret h op
