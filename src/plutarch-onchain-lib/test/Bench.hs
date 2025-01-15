{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Plutarch.Prelude
import Plutarch.Internal.Lift
import Plutarch.Test.Bench
import Plutarch.Monadic qualified as P
import Plutarch.LedgerApi.V3
import Plutarch.Core.List
import Plutarch.Core.Utils (pcanFind)
import Plutarch.Core.FieldBinds 
import Plutarch.Core.ValidationLogic (penforceNSpendRedeemers)
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
      , testGroup "Count Spend" countSpendBenches
      --, testGroup "Spending Purpose" spendingPurposeBenches
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
  [ bench "optional" (pisJust #$ pfind # plam (#== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  , bench "bool" (pcanFind # plam (#== 5) # pconstant @(PBuiltinList PInteger) [1..200])
  ]

countSpendBenches :: [TestTree]
countSpendBenches =
  [ bench "fastNSpends" 
      (penforceNSpendRedeemers 100 (pconstant exampleRedeemers))
  ]

spendingPurposeBenches :: [TestTree]
spendingPurposeBenches =
  [ bench "generic" 
      (mkValidatorGeneric # pconstant (mkScriptContext 2))
  , bench "specialized"  
      (mkValidatorSpecialized # pconstant (mkScriptContext 2))
  ]

mkValidatorGeneric :: ClosedTerm (PScriptContext :--> PUnit) 
mkValidatorGeneric = plam $ \ctx -> P.do 
  ctxF <- pletFields @'["txInfo", "redeemer", "scriptInfo"] ctx
  PSpendingScript scriptInfo <- pmatch ctxF.scriptInfo
  scriptInfoF <- pletFields @'["_1"] scriptInfo
  PDJust ownInDat <- pmatch scriptInfoF._1
  pif (pfromData (punsafeCoerce @(PAsData PInteger) (pto ownInDat)) #> 0) (pconstant ()) perror

mkValidatorSpecialized :: ClosedTerm (PScriptContext :--> PUnit) 
mkValidatorSpecialized = plam $ \ctx -> P.do 
  ctxF <- pletFields @'["txInfo", "redeemer", "scriptInfo"] ctx
  scriptInfoF <- pletFieldsSpending ctxF.scriptInfo
  PDJust ownInDat <- pmatch scriptInfoF._1
  pif (pfromData (punsafeCoerce @(PAsData PInteger) (pto ownInDat)) #> 0) (pconstant ()) perror