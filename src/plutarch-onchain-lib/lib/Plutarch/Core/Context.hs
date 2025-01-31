module Plutarch.Core.Context (
paddressCredential, ptxOutAddress, ptxOutCredential, ptxOutValue, ptxInInfoResolved, ptxInInfoOutRef, pscriptContextTxInfo, ptxInfoSignatories) where 

import Plutarch.Prelude ( Term, pmatch, PAsData, PBuiltinList )
import Plutarch.LedgerApi.V3
    ( AmountGuarantees(Positive),
      PValue,
      PAddress(paddress'credential),
      PCredential,
      PTxOut(ptxOut'value, ptxOut'address),
      PTxInInfo(ptxInInfo'outRef, ptxInInfo'resolved),
      PTxOutRef, PScriptContext, PTxInfo, pscriptContext'txInfo, PPubKeyHash, ptxInfo'signatories )
import qualified Plutarch.LedgerApi.AssocMap as AssocMap

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