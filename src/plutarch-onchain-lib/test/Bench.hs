{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Plutarch.Prelude
import Plutarch.Internal.Lift
import Plutarch.Test.Bench
import Plutarch.Monadic qualified as P
import Plutarch.LedgerApi.V3
import Plutarch.Core.List
import Plutarch.Core.FieldBinds
import Plutarch.Core.ValidationLogic
import Plutarch.Core.Unroll
import Plutarch.Maybe
import Plutarch.Internal.Term
import Test.Tasty (TestTree, testGroup)
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value
import PlutusLedgerApi.V3 (OutputDatum (NoOutputDatum), PubKeyHash (..), Redeemer (..),
                           ScriptContext (..), ScriptInfo (SpendingScript), TxId (..), TxInfo (..),
                           TxOut (..), TxOutRef (..), always, Datum(..), ScriptPurpose(..))
import PlutusTx qualified
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Builtins qualified as PlutusTx

-- | A very crude deterministic generator for 'ScriptContext's with size
-- approximately proportional to the input integer.
mkScriptContext :: Int -> ScriptContext
mkScriptContext i =
  ScriptContext
    (mkTxInfo i)
    (Redeemer (PlutusTx.toBuiltinData (1 :: Integer)))
    (SpendingScript (TxOutRef (TxId "") 0) (Just (Datum $ PlutusTx.toBuiltinData @Integer 1)))

emptyMintValue :: Value
emptyMintValue = mempty

mkRedeemer :: Integer -> Redeemer
mkRedeemer i = Redeemer (PlutusTx.toBuiltinData i)

mkScriptPurpose :: Integer -> ScriptPurpose
mkScriptPurpose i = Spending (TxOutRef (TxId "") i)

mkTxInfo :: Int -> TxInfo
mkTxInfo i = TxInfo {
  txInfoInputs=mempty,
  txInfoReferenceInputs=mempty,
  txInfoOutputs=fmap mkTxOut [1..i],
  txInfoFee=10000,
  txInfoMint=emptyMintValue,
  txInfoTxCerts=mempty,
  txInfoWdrl=Map.empty,
  txInfoValidRange=always,
  txInfoSignatories=mempty,
  txInfoRedeemers=Map.unsafeFromList $ fmap (\(fromIntegral -> x) -> (mkScriptPurpose x, mkRedeemer x)) [1..i],
  txInfoData=Map.empty,
  txInfoId=TxId "",
  txInfoVotes=Map.empty,
  txInfoProposalProcedures=mempty,
  txInfoCurrentTreasuryAmount=Nothing,
  txInfoTreasuryDonation=Nothing
  }

mkTxOut :: Int -> TxOut
mkTxOut i = TxOut {
  txOutAddress=pubKeyHashAddress (PubKeyHash ""),
  txOutValue=mkValue i,
  txOutDatum=NoOutputDatum,
  txOutReferenceScript=Nothing
  }

mkValue :: Int -> Value
mkValue i = assetClassValue (assetClass adaSymbol adaToken) (fromIntegral i)

exampleContext :: ScriptContext
exampleContext = mkScriptContext 100

exampleRedeemers :: Map.Map ScriptPurpose Redeemer
exampleRedeemers = Map.unsafeFromList $ fmap (\x -> (mkScriptPurpose x, mkRedeemer x)) [1..100]

main :: IO ()
main =
  defaultMain $
    testGroup
      "Benchmarks"
      [ testGroup "Drops" dropBenches
      , testGroup "Lengths" lengthBenches
      , testGroup "Is Unique" isUniqueSetBenches
      , testGroup "Find" findBenches
      , testGroup "Count Spend Scripts" countSpendBenches
      , testGroup "Elem At" elemAtBenches
      , testGroup "Unroll" unrollBench
      ]

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
  [ bench "optional" (pisJust #$ pfind # plam (#== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  , bench "bool" (pcanFind # plam (#== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  , bench "try" (pmustFind # plam (#== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  ]

countSpendBenches :: [TestTree]
countSpendBenches =
  [ bench "recursive" $ pcountSpendRedeemers (pconstant exampleRedeemers) #== 100
  , bench "fast"
      (penforceNSpendRedeemers 100 (pconstant exampleRedeemers))
  ]

elemAtBenches :: [TestTree]
elemAtBenches =
  [ bench "recursive" $ pelemAt' # 199 # pconstant @(PBuiltinList PInteger) [1..200]
  , bench "fast" $ pelemAtFast # pconstant @(PBuiltinList PInteger) [1..200] # 199 
  ]

unrollLengthBound :: forall list a s. PIsListLike list a => Term s (list a :--> PInteger)
unrollLengthBound = punrollBound 200 (const $ plam $ \_ -> pconstant (-1)) go 0
  where
    go ::
      (Integer -> Term s (list a :--> PInteger)) ->
      Integer ->
      Term s (list a :--> PInteger)
    go self n = plam $ pelimList (\_ xs -> self (n + 1) # xs) (pconstant n)

unrollBench :: [TestTree]
unrollBench =
  [ bench "bounded-unroll length" $ unrollLengthBound # pconstant @(PBuiltinList PInteger) [1..200]
  , bench "no-unroll recursive length" $ plength # pconstant @(PBuiltinList PInteger) [1..200]
  ]