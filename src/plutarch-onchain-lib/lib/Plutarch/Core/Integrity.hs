module Cardano.Core.Integrity (
  pisScriptCredential,
  pisPubKeyCredential,
  pdeserializeCredential,
) where

import Plutarch.Core.List
import Plutarch.Prelude

-- | Check that a data-encoded Credential is a ScriptCredential.
-- This does not guarantee that the data-encoded term is structurally a valid Credential.
-- So this should only be used if the data-encoded term is known to be a Credential.
-- If the term is obtained from relevant fields of the ScriptContext or TxInfo, then this check is safe
-- because the ledger guarantees the structural validity of the Credential.
pisScriptCredential :: Term s (PAsData PCredential) -> Term s PBool
pisScriptCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 1

-- | Check if the provided data-encoded Credential is a PubKeyCredential.
-- This does not guarantee that the data-encoded term is structurally a valid Credential.
-- So this should only be used if the data-encoded term is known to be a Credential.
-- If the term is obtained from relevant fields of the ScriptContext or TxInfo, then this check is safe
-- because the ledger guarantees the structural validity of the Credential.
pisPubKeyCredential :: Term s (PAsData PCredential) -> Term s PBool
pisPubKeyCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 0

-- | Check if the provided data-encoded term has the expected builtin data representation of a credential.
pdeserializeCredential :: Term s (PAsData PCredential) -> Term s (PAsData PCredential)
pdeserializeCredential term =
  plet (pasConstr # pforgetData term) $ \constrPair ->
    plet (pfstBuiltin # constrPair) $ \constrIdx ->
      pif (plengthBS # (pasByteStr # (pheadSingleton # (psndBuiltin # constrPair))) #== 28)
          (
            pcond
              [ ( constrIdx #== 0 , term)
              , ( constrIdx #== 1 , term)
              ]
              (ptraceInfoError "Invalid credential")
          )
          perror
