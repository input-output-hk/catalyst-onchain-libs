{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo       #-}
{-| Tests for Plutarch.Core.List
-}
module Plutarch.MerkleTree.Test(
  tests
) where

import           Plutarch.Prelude                                                     
import qualified Plutarch.Monadic                     as P
import           Test.QuickCheck.Instances.ByteString ()
import           Test.Tasty
import           Test.Tasty.HUnit
import           Plutarch.Test.Unit (testEval)

tests :: TestTree
tests = testGroup "List Utilities"
  [ testEval "ptails10" ptails10
  ]