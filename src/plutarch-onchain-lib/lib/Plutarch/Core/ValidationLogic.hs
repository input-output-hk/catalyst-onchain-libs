{-# LANGUAGE NamedFieldPuns #-}

module Plutarch.Core.ValidationLogic (
  penforceNSpendRedeemers
  , pcountSpendRedeemers
  , pcountScriptInputs
  , pcountInputsFromCred
  , pvalidateConditions
  , pvalueFromCred
  , pvalueToCred
  , pemptyLedgerValue
  , pinputsFromCredential
) where

import Plutarch.Core.Context (paddressCredential, ptxInInfoResolved,
                              ptxOutCredential)
import Plutarch.Core.List (pdropFast)
import Plutarch.Core.Utils (pand'List)
import Plutarch.LedgerApi.AssocMap qualified as AssocMap
import Plutarch.LedgerApi.V3 (AmountGuarantees (..), KeyGuarantees (..),
                              PCredential (..), PRedeemer, PScriptPurpose,
                              PTxInInfo, PTxOut (..), PValue)
import Plutarch.Prelude (ClosedTerm, PAsData, PBool, PBuiltinList, PBuiltinPair,
                         PEq ((#==)), PInteger, PList,
                         PListLike (pcons, pelimList, phead, pnil, ptail),
                         PUnit, S, Term, pasConstr, pconstant, perror, pfix,
                         pforgetData, pfromData, pfstBuiltin, phoistAcyclic,
                         pif, plam, plet, pmatch, pnot, pto, type (:-->), (#$),
                         (#))
import Plutarch.Unsafe (punsafeCoerce)
import PlutusLedgerApi.V3 (Value)

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

-- | Count the number of script inputs in the transaction inputs list.
pcountScriptInputs :: Term s (PBuiltinList (PAsData PTxInInfo) :--> PInteger)
pcountScriptInputs =
  phoistAcyclic $
    let go :: Term s (PInteger :--> PBuiltinList (PAsData PTxInInfo) :--> PInteger)
        go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let cred = ptxOutCredential $ ptxInInfoResolved (pfromData x)
                   in pmatch cred $ \case
                        PScriptCredential _ -> self # (n + 1) # xs
                        _ -> self # n # xs
                )
                n
     in go # 0

-- | Count the number of transaction inputs from the provided credential.
pcountInputsFromCred :: Term (s :: S) (PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PInteger)
pcountInputsFromCred =
  phoistAcyclic $ plam $ \cred txIns ->
    let go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let inputCred = ptxOutCredential $ ptxInInfoResolved $ pfromData x
                   in pif (cred #== inputCred) (self # (n + 1) # xs) (self # n # xs)
                )
                n
     in go # 0 # txIns

emptyValue :: Value
emptyValue = mempty

pemptyLedgerValue :: ClosedTerm (PValue 'Sorted 'Positive)
pemptyLedgerValue = punsafeCoerce $ pconstant @(PValue 'Unsorted 'NoGuarantees) emptyValue

-- | Return the total value spent by all the transaction inputs that are from the provided credential.
pvalueFromCred :: Term s (PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PValue 'Sorted 'Positive)
pvalueFromCred = phoistAcyclic $ plam $ \cred inputs ->
  (pfix #$ plam $ \self acc ->
    pelimList
      (\txIn xs ->
        self
          # pmatch (ptxInInfoResolved (pfromData txIn)) (\(PTxOut {ptxOut'address, ptxOut'value}) ->
              pif (paddressCredential ptxOut'address #== cred)
                  (acc <> pfromData ptxOut'value)
                  acc)
          # xs
      )
      acc
  )
  # pemptyLedgerValue
  # inputs

-- | Return the total value produced by all the transaction outputs that are to the provided credential.
pvalueToCred :: Term s (PCredential :--> PBuiltinList (PAsData PTxOut) :--> PValue 'Sorted 'Positive)
pvalueToCred = phoistAcyclic $ plam $ \cred inputs ->
  let value = (pfix #$ plam $ \self acc ->
                pelimList
                  (\txOut xs ->
                    self
                      # pmatch (pfromData txOut) (\(PTxOut {ptxOut'address, ptxOut'value}) ->
                          pif (paddressCredential ptxOut'address #== cred)
                              (acc <> pfromData ptxOut'value)
                              acc)
                      # xs
                  )
                  acc
              )
              # pemptyLedgerValue
              # inputs
  in value

-- | Return the transaction inputs that are from the provided credential.
pinputsFromCredential :: Term s (PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PList PTxOut)
pinputsFromCredential = phoistAcyclic $ plam $ \cred txIns ->
  let go = pfix #$ plam $ \self acc ->
            pelimList
              (\x xs ->
                  plet (ptxInInfoResolved $ pfromData x) $ \txInOut->
                    let inputCred = ptxOutCredential txInOut
                    in pif (cred #== inputCred) (self # (pcons # txInOut # acc) # xs) (self # acc # xs)
              )
              acc
   in go # pnil @PList # txIns

-- | Strictly evaluates a list of boolean expressions.
-- If all the expressions evaluate to true, returns unit, otherwise throws an error.
pvalidateConditions :: [Term s PBool] -> Term s PUnit
pvalidateConditions conds =
  pif (pand'List conds)
      (pconstant ())
      perror
