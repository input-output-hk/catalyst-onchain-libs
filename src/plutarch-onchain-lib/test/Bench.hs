module Main (main) where

import Plutarch.Prelude
import Plutarch.Internal.Lift
import Plutarch.Test.Bench 
import Plutarch.Core.List
import Plutarch.Core.Utils (pcanFind)
import Plutarch.Maybe
import Test.Tasty (TestTree, testGroup)

main :: IO ()
main =
  defaultMain $
    testGroup
      "Benchmarks"
      [ testGroup "Drops" dropBenches
      , testGroup "Lengths" lengthBenches
      , testGroup "Is Unique" isUniqueSetBenches
      , testGroup "Find" findBenches
      ]

-- Suites

dropBenches :: [TestTree]
dropBenches =
  [ bench "recursive" (pdropR # 500 # pconstant @(PBuiltinList PInteger) [1..500])
  , bench "fast" (pdropFast # 500 # pconstant @(PBuiltinList PInteger) [1..500])
  ]

lengthBenches :: [TestTree]
lengthBenches =
  [ bench "recursive" (plength # pconstant @(PBuiltinList PInteger) [1..500])
  , bench "fast" (pbuiltinListLengthFast # 500 # pconstant @(PBuiltinList PInteger) [1..500])
  ]

isUniqueSetBenches :: [TestTree]
isUniqueSetBenches =
  [ bench "pow2" (_pIsUnique # pconstant @(PBuiltinList PInteger) [1..200])
  , bench "bit trick" (pisUniqueSet # 200 # pconstant @(PBuiltinList PInteger) [1..200])
  ]

findBenches :: [TestTree]
findBenches =
  [ bench "optional" (pisJust #$ pfind # plam (\x -> x #== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  , bench "bool" (pcanFind # plam (\x -> x #== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  ]