{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo       #-}
{-| Tests for Plutarch.Core.List
-}
module Plutarch.Value.Test(
  tests
) where

import Plutarch.Core.Value
import Plutarch.LedgerApi.V3
import Plutarch.Prelude
import Plutarch.Test.Unit (testEvalEqual)
import PlutusLedgerApi.V1.Value
import PlutusTx.AssocMap (unsafeFromList)
import Test.Tasty

exampleInputValueA :: Value
exampleInputValueA = Value $ unsafeFromList [
  (CurrencySymbol "", unsafeFromList [(TokenName "", 3000000)]),
  (CurrencySymbol "progCS", unsafeFromList [(TokenName "foo", 100), (TokenName "bar", 200)]),
  (CurrencySymbol "usdCS", unsafeFromList [(TokenName "usdt", 50)]),
  (CurrencySymbol "nftCS", unsafeFromList [(TokenName "artnft", 1)])
  ]

pexampleInputValueA :: ClosedTerm (PAsData (PValue 'Unsorted 'NoGuarantees))
pexampleInputValueA = pconstant exampleInputValueA

exampleOutputValueA :: Value
exampleOutputValueA = Value $ unsafeFromList [
  (CurrencySymbol "", unsafeFromList [(TokenName "", 3000000)]),
  (CurrencySymbol "progCS", unsafeFromList [(TokenName "foo", 140), (TokenName "bar", 60)]),
  (CurrencySymbol "usdCS", unsafeFromList [(TokenName "usdt", 50)]),
  (CurrencySymbol "nftCS", unsafeFromList [(TokenName "artnft", 1)])
  ]

pexampleOutputValueA :: ClosedTerm (PAsData (PValue 'Unsorted 'NoGuarantees))
pexampleOutputValueA = pconstant exampleOutputValueA

tests :: TestTree
tests = testGroup "Value Utilities"
  [ testGroup "Succeed / EvalEqual Tests"
      [ testEvalEqual "pvalueEqualsDeltaCurrencySymbol"
          (pvalueEqualsDeltaCurrencySymbol # pconstant @PCurrencySymbol (CurrencySymbol "progCS") # pexampleInputValueA # pexampleOutputValueA)
          (pconstant [(TokenName "foo", -40), (TokenName "bar", 140)])
      ]
  ]
