module Main where

import qualified Plutarch.MerkleTree.Test as MerkleTree
import           Test.Tasty               (TestTree, defaultMain, testGroup)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "plutarch"
  [ MerkleTree.tests
  ]
