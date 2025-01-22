module Main where

import qualified Plutarch.MerkleTree.Test as MerkleTree
import qualified Plutarch.List.Test as List
import           Test.Tasty               (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutarch"
  [ MerkleTree.tests
  , List.tests 
  ]
