module Main where

import qualified MyLib (someFunc)
import Yocto

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  MyLib.someFunc
