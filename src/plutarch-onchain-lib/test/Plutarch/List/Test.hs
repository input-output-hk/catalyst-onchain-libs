{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo       #-}
{-| Tests for Plutarch.Core.List
-}
module Plutarch.List.Test(
  tests
) where

import Plutarch.Core.List
import Plutarch.Prelude
import Plutarch.Test.Unit (testEvalEqual, testEvalFail)
import Test.Tasty

exampleInts :: [Integer]
exampleInts = [1..100]

tepnTails :: [Integer]
tepnTails = drop 10 exampleInts

tests :: TestTree
tests = testGroup "List Utilities"
  [ testGroup "Succeed / EvalEqual Tests"
      [ testEvalEqual "ptails10" (ptails10 # pconstant @(PBuiltinList PInteger) [1..100]) (pconstant @(PBuiltinList PInteger) tepnTails)
      , testEvalEqual "pheadSingleton" (pheadSingleton # pconstant @(PBuiltinList PInteger) [1]) (pconstant @PInteger 1)
      , testEvalEqual "pmustFind"
          (pmustFind # plam (#== 6) # pconstant @(PBuiltinList PInteger) [1..6])
          (pconstant @PInteger 6)
      ]
  , testGroup "EvalFail Tests"
      [ testEvalFail "pheadSingleton 2 elements" (pheadSingleton # pconstant @(PBuiltinList PInteger) [1,2])
      , testEvalFail "pheadSingleton empty list" (pheadSingleton # pconstant @(PBuiltinList PInteger) [])
      , testEvalFail "pmustFind" $ pmustFind # plam (#== 6) # pconstant @(PBuiltinList PInteger) [1..5]
      ]
  ]
