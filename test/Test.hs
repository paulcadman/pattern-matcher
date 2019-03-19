module Main where

import Calculus

import Test.QuickCheck


main :: IO ()
main = quickCheckWith stdArgs { maxSuccess = 10000 } semanticPreservation
