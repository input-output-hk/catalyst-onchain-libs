{-# LANGUAGE OverloadedRecordDot #-}

module Plutarch.Core.ValidationLogic where

import Plutarch.Prelude
import Plutarch.LedgerApi.V3 (PScriptPurpose, PRedeemer, PCredential (..), PTxInInfo, PValue, KeyGuarantees(..), AmountGuarantees (..), PTxOut)
import qualified Plutarch.LedgerApi.AssocMap as AssocMap
import Plutarch.Core.List (pdropFast)
import Plutarch.Core.Utils (pand'List)
import PlutusLedgerApi.V3 (Value)
import Plutarch.Unsafe (punsafeCoerce)

{- | Check that there is exactly n spend plutus scripts executed in the transaction via the txInfoRedeemers list.
    Assumes that the txInfoRedeemers list is sorted according to the ledger Ord instance for PlutusPurpose:
    `deriving instance Ord (ConwayPlutusPurpose AsIx era)`
    See: https://github.com/IntersectMBO/cardano-ledger/blob/d79d41e09da6ab93067acddf624d1a540a3e4e8d/eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs#L188

    This assumption holds true for any valid transaction, because it is enforced by the ledger rules.
-}
penforceNSpendRedeemers :: forall {s :: S}. Term s PInteger -> Term s (AssocMap.PMap 'AssocMap.Unsorted PScriptPurpose PRedeemer) -> Term s PBool
penforceNSpendRedeemers n rdmrs =
    let isNonSpend :: Term (w :: S) (PAsData PScriptPurpose) -> Term (w :: S) PBool
        isNonSpend red = pnot # (pfstBuiltin # (pasConstr # pforgetData red) #== 1)

        isLastSpend :: Term (s :: S) (PBuiltinList (PBuiltinPair (PAsData PScriptPurpose) (PAsData PRedeemer)) :--> PBool)
        isLastSpend = plam $ \redeemers ->
          let constrPair :: Term s (PAsData PScriptPurpose)
              constrPair = pfstBuiltin # (phead # redeemers)
              constrIdx = pfstBuiltin # (pasConstr # pforgetData constrPair)
           in pif
                (constrIdx #== 1)
                (pelimList (\x _ -> isNonSpend (pfstBuiltin # x)) (pconstant True) (ptail # redeemers))
                perror
     in isLastSpend # (pdropFast # (n - 1) # pto rdmrs)

{- | Count the number of spend plutus scripts executed in the transaction via the txInfoRedeemers list.
    Assumes that the txInfoRedeemers list is sorted according to the ledger Ord instance for PlutusPurpose:
    `deriving instance Ord (ConwayPlutusPurpose AsIx era)`
    See: https://github.com/IntersectMBO/cardano-ledger/blob/d79d41e09da6ab93067acddf624d1a540a3e4e8d/eras/conway/impl/src/Cardano/Ledger/Conway/Scripts.hs#L188
    
    This assumption holds true for any valid transaction, because it is enforced by the ledger rules.
-}
pcountSpendRedeemers :: forall {s :: S}. Term s (AssocMap.PMap 'AssocMap.Unsorted PScriptPurpose PRedeemer) -> Term s PInteger
pcountSpendRedeemers rdmrs =
    let go :: Term (s :: S) (PInteger :--> PBuiltinList (PBuiltinPair (PAsData PScriptPurpose) (PAsData PRedeemer)) :--> PInteger)
        go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let constrPair :: Term (s :: S) (PAsData PScriptPurpose)
                      constrPair = pfstBuiltin # x
                      constrIdx = pfstBuiltin # (pasConstr # pforgetData constrPair)
                  in pif (constrIdx #== 1) (self # (n + 1) # xs) n
                )
                n
     in go # 0 # pto rdmrs

pcountScriptInputs :: Term s (PBuiltinList PTxInInfo :--> PInteger)
pcountScriptInputs =
  phoistAcyclic $
    let go :: Term s (PInteger :--> PBuiltinList PTxInInfo :--> PInteger)
        go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let cred = pfield @"credential" # (pfield @"address" # (pfield @"resolved" # x))
                   in pmatch cred $ \case
                        PScriptCredential _ -> self # (n + 1) # xs
                        _ -> self # n # xs
                )
                n
     in go # 0     

pcountInputsFromCred :: Term (s :: S) (PAsData PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PInteger)
pcountInputsFromCred =
  phoistAcyclic $ plam $ \cred txIns ->
    let go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let inputCred = pfield @"credential" # (pfield @"address" # (pfield @"resolved" # x))
                   in pif (cred #== inputCred) (self # (n + 1) # xs) (self # n # xs)
                )
                n
     in go # 0 # txIns

emptyValue :: Value
emptyValue = mempty

pemptyLedgerValue :: ClosedTerm (PValue 'Sorted 'Positive)
pemptyLedgerValue = punsafeCoerce $ pconstant @(PValue 'Unsorted 'NoGuarantees) emptyValue

pvalueFromCred :: Term s (PAsData PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PValue 'Sorted 'Positive)
pvalueFromCred = phoistAcyclic $ plam $ \cred inputs ->
  (pfix #$ plam $ \self acc ->
    pelimList
      (\txIn xs ->
        self
          # pletFields @'["address", "value"] (pfield @"resolved" # txIn) (\txInF ->
                pif ((pfield @"credential" # txInF.address) #== cred)
                    (acc <> pfromData txInF.value)  
                    acc
                    )
          # xs
      )
      acc
  )
  # pemptyLedgerValue
  # inputs

pvalueToCred :: Term s (PAsData PCredential :--> PBuiltinList (PAsData PTxOut) :--> PValue 'Sorted 'Positive)
pvalueToCred = phoistAcyclic $ plam $ \cred inputs ->
  let value = (pfix #$ plam $ \self acc ->
                pelimList
                  (\txOut xs ->
                    self
                      # pletFields @'["address", "value"] txOut (\txOutF ->
                          plet txOutF.address $ \addr ->
                            pif (pfield @"credential" # addr #== cred)
                                (acc <> pfromData txOutF.value)
                                acc
                                )
                      # xs
                  )
                  acc
              )
              # pemptyLedgerValue
              # inputs
  in value
  
-- | Strictly evaluates a list of boolean expressions.
-- If all the expressions evaluate to true, returns unit, otherwise throws an error.
pvalidateConditions :: [Term s PBool] -> Term s PUnit
pvalidateConditions conds =
  pif (pand'List conds)
      (pconstant ())
      perror
