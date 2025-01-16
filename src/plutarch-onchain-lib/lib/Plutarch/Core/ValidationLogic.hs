module Plutarch.Core.ValidationLogic where

import Plutarch.Prelude
import Plutarch.LedgerApi.V3 (PScriptPurpose, PRedeemer)
import qualified Plutarch.LedgerApi.AssocMap as AssocMap
import Plutarch.Core.List (pdropFast)

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