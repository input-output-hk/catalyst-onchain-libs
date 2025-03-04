module Plutarch.Core.Context (
  paddressCredential,
  ptxOutAddress,
  ptxOutCredential,
  ptxOutValue,
  ptxInInfoResolved,
  ptxInInfoOutRef,
  pscriptContextTxInfo,
  ptxInfoSignatories,
  ptxOutInlineDatumRaw,
  ptxOutDatum,
  ) where

import Plutarch.Internal.Other
import Plutarch.LedgerApi.AssocMap qualified as AssocMap
import Plutarch.LedgerApi.V3 (AmountGuarantees (Positive),
                              PAddress (paddress'credential), PCredential,
                              POutputDatum (POutputDatum), PPubKeyHash,
                              PScriptContext,
                              PTxInInfo (ptxInInfo'outRef, ptxInInfo'resolved),
                              PTxInfo,
                              PTxOut (ptxOut'address, ptxOut'datum, ptxOut'value),
                              PTxOutRef, PValue, pscriptContext'txInfo,
                              ptxInfo'signatories)
import Plutarch.Prelude (PAsData, PBuiltinList, PData, Term, perror, pmatch)

paddressCredential :: Term s PAddress -> Term s PCredential
paddressCredential addr =
  pmatch addr $ \addr' ->
    paddress'credential addr'

ptxOutAddress :: Term s PTxOut -> Term s PAddress
ptxOutAddress =
  flip pmatch $ \txo ->
    ptxOut'address txo

ptxOutCredential :: Term s PTxOut -> Term s PCredential
ptxOutCredential =
  paddressCredential . ptxOutAddress

ptxOutValue :: Term s PTxOut -> Term s (PAsData (PValue 'AssocMap.Sorted 'Positive))
ptxOutValue =
  flip pmatch $ \txo ->
    ptxOut'value txo

ptxOutDatum :: Term s PTxOut -> Term s POutputDatum
ptxOutDatum =
  flip pmatch $ \txo ->
    ptxOut'datum txo

ptxOutInlineDatumRaw :: Term s PTxOut -> Term s PData
ptxOutInlineDatumRaw =
  flip pmatch $ \txo ->
    pmatch (ptxOut'datum txo) $ \case
     (POutputDatum d) -> (pto d)
     _ -> perror

ptxInInfoResolved :: Term s PTxInInfo -> Term s PTxOut
ptxInInfoResolved txInInfo =
  pmatch txInInfo $ \txInInfo' ->
    ptxInInfo'resolved txInInfo'

ptxInInfoOutRef :: Term s PTxInInfo -> Term s PTxOutRef
ptxInInfoOutRef txInInfo =
  pmatch txInInfo $ \txInInfo' ->
    ptxInInfo'outRef txInInfo'

pscriptContextTxInfo :: Term s PScriptContext -> Term s PTxInfo
pscriptContextTxInfo ctx =
  pmatch ctx $ \ctx' ->
    pscriptContext'txInfo ctx'

ptxInfoSignatories :: Term s PTxInfo -> Term s (PAsData (PBuiltinList (PAsData PPubKeyHash)))
ptxInfoSignatories =
  flip pmatch $ \txInfo ->
    ptxInfo'signatories txInfo
