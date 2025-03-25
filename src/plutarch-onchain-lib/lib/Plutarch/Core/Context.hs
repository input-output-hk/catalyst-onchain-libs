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
  paddressStakingCredential,
  paddressMaybeStakingCredential,
  pconstructExpectedOutput,
  pconstructExpectedOutputWithOutputDatum,
  ) where

import Plutarch.Core.Integrity (pfromJustData)
import Plutarch.LedgerApi.AssocMap qualified as AssocMap
import Plutarch.LedgerApi.V3 (AmountGuarantees (Positive),
                              KeyGuarantees (Sorted),
                              PAddress (paddress'credential, paddress'stakingCredential),
                              PCredential, PDatum (PDatum), PMaybeData,
                              POutputDatum (POutputDatum), PPubKeyHash,
                              PScriptContext (pscriptContext'txInfo),
                              PStakingCredential,
                              PTxInInfo (ptxInInfo'outRef, ptxInInfo'resolved),
                              PTxInfo (ptxInfo'signatories), PTxOut (..),
                              PTxOutRef, PValue)
import Plutarch.Prelude (PAsData, PBuiltinList, PData, Term, pcon, pconstant,
                         pdata, perror, pmatch, pto)

paddressCredential :: Term s PAddress -> Term s PCredential
paddressCredential addr =
  pmatch addr $ \addr' ->
    paddress'credential addr'

paddressMaybeStakingCredential :: Term s PAddress -> Term s (PMaybeData PStakingCredential)
paddressMaybeStakingCredential addr =
  pmatch addr $ \addr' ->
    paddress'stakingCredential addr'

paddressStakingCredential :: Term s PAddress -> Term s PStakingCredential
paddressStakingCredential addr =
  pmatch addr $ \addr' ->
    pfromJustData $ paddress'stakingCredential addr'

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

pconstructExpectedOutput :: Term s PAddress -> Term s (PAsData (PValue 'Sorted 'Positive)) -> Term s PData -> Term s (PAsData PTxOut)
pconstructExpectedOutput address value datum =
  pdata $ pcon $
    PTxOut
     { ptxOut'address = address
     , ptxOut'value = value
     , ptxOut'datum = pcon $ POutputDatum $ pcon $ PDatum datum
     , ptxOut'referenceScript = pconstant Nothing
     }

pconstructExpectedOutputWithOutputDatum :: Term s PAddress -> Term s (PAsData (PValue 'Sorted 'Positive)) -> Term s POutputDatum -> Term s (PAsData PTxOut)
pconstructExpectedOutputWithOutputDatum address value datum =
  pdata $ pcon $
    PTxOut
     { ptxOut'address = address
     , ptxOut'value = value
     , ptxOut'datum = datum
     , ptxOut'referenceScript = pconstant Nothing
     }
