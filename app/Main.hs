module Main (main) where

import Control.Monad (when)
import qualified Data.ByteString as BS
import Data.Char
import System.Directory (doesFileExist)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath (takeExtension, takeBaseName)

import R1CSParser

capitalised :: String -> String
capitalised (head:tail) = toUpper head : tail
capitalised [] = []

failure :: IO ()
failure = do
  putStrLn "usage: *.r1cs"
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fname] -> do
         let ext = takeExtension fname
         exists <- doesFileExist fname
         when ((not exists) || (ext /= ".r1cs")) failure
         fcontent <- BS.readFile fname
         case parseR1CSIR fcontent of
           Left e -> print e
           Right (config, constrs, _) -> putStrLn (toLean (capitalised $ takeBaseName fname) config constrs)
    _ -> failure
