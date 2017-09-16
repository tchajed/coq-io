module Interpreter where

import Prog
import System.IO

diskInterpret :: Handle -> DiskOp a -> IO a
diskInterpret h (Read a) = do
  hSeek h AbsoluteSeek a
  c <- hGetChar h
  return $ unsafeCoerce c
diskInterpret h (Write a v) = do
  hSeek h AbsoluteSeek a
  hPutChar h v
  return $ unsafeCoerce ()

interpret :: Handle -> DiskProg a -> IO a
interpret _ (Ret a) = return a
interpret h (Bind p p') = do
  r <- interpret h p
  interpret h (p' r)
interpret h (Primitive op) = unsafeCoerce <$> diskInterpret h op
