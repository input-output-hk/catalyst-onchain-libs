module Main where

import Plutarch.List.Test qualified as List
import Plutarch.MerkleTree.Test qualified as MerkleTree
import Test.Tasty (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutarch"
  [ MerkleTree.tests
  , List.tests
  ]
