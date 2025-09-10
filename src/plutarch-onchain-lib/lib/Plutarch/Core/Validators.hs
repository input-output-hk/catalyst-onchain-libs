{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE QualifiedDo    #-}
module Plutarch.Core.Validators (
  mkNFTMinting,
  alwaysFailScript,
  mkPermissionedValidator,
) where

import Plutarch.Core.Context (pscriptContextTxInfo, ptxInfoSignatories)
import Plutarch.Core.List (pheadSingleton)
import Plutarch.Core.Utils (phasUTxO, ptxSignedByPkh)
import Plutarch.Core.ValidationLogic (pvalidateConditions)
import Plutarch.Core.Value (ptryLookupValue)
import Plutarch.LedgerApi.V3 (PPubKeyHash, PScriptContext (..),
                              PScriptInfo (..), PTxInfo (PTxInfo), PTxOutRef,
                              ptxInfo'inputs, ptxInfo'mint)
import Plutarch.Monadic qualified as P
import Plutarch.Prelude (PAsData, PData, PEq ((#==)), PUnit, Term, pconstant,
                         perror, pfromData, pfstBuiltin, plam, plet, pmatch,
                         psndBuiltin, type (:-->), (#))
import PlutusLedgerApi.V3 (TokenName)

-- | A one-shot minting policy that allows minting a single token with a given token name.
-- Arguments:
--   1. The token name to mint (Haskell level argument)
--   2. The UTxO reference of the protocol parameters UTxO.
mkNFTMinting :: TokenName -> (forall s . Term s (PTxOutRef :--> PScriptContext :--> PUnit))
mkNFTMinting tn = plam $ \oref ctx -> P.do
  PScriptContext {pscriptContext'txInfo, pscriptContext'scriptInfo} <- pmatch ctx
  PTxInfo {ptxInfo'inputs, ptxInfo'mint} <- pmatch pscriptContext'txInfo
  PMintingScript ownCS <- pmatch pscriptContext'scriptInfo
  mintedValue <- plet $ pfromData ptxInfo'mint
  let ownTkPairs = ptryLookupValue # ownCS # mintedValue
  -- Enforce that only a single token name is minted for this policy
  ownTkPair <- plet (pheadSingleton # ownTkPairs)
  ownTokenName <- plet (pfstBuiltin # ownTkPair)
  ownNumMinted <- plet (psndBuiltin # ownTkPair)
  pvalidateConditions
    [ ownTokenName #== pconstant tn
    , ownNumMinted #== pconstant 1
    , phasUTxO # oref # pfromData ptxInfo'inputs
    ]

-- | Permissioned Validator
-- This validator checks for a given permissioned credential in the signatories of the transaction.
-- Arguments:
--   1. Arbitrary BuiltinData used to provide a nonce to the script to allow the caller to create multiple
--      instances with different script hashes.
--   2. The permissioned credential that must be present in the signatories of the transaction.
mkPermissionedValidator :: forall s . Term s (PData :--> PAsData PPubKeyHash :--> PScriptContext :--> PUnit)
mkPermissionedValidator = plam $ \_ permissionedCred ctx ->
  pvalidateConditions
    [ ptxSignedByPkh # permissionedCred # (pfromData . ptxInfoSignatories . pscriptContextTxInfo) ctx
    ]

-- | A nonced always fails script
-- The parameter is used to modify the script hash.
-- This is where the protocol parameters UTxO should reside.
-- Argument:
--  1. Arbitrary BuiltinData used to provide a nonce to the script to allow the caller to create multiple
--     instances with different script hashes.
alwaysFailScript :: forall s . Term s (PData :--> PScriptContext :--> PUnit)
alwaysFailScript = plam $ \_ _ctx -> perror
