module Plutarch.Core.ValidationLogic where

import Plutarch.Prelude
import Plutarch.LedgerApi.V3 (PScriptPurpose, PRedeemer)
import qualified Plutarch.LedgerApi.AssocMap as AssocMap
import Plutarch.Core.List (pdropFast)

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