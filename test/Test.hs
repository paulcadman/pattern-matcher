module Main where

import Calculus

import Test.QuickCheck


main :: IO ()
main = quickCheck (withMaxSuccess 10000 semanticPreservation)
