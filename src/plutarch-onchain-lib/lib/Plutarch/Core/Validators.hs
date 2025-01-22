{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE QualifiedDo         #-}
module Plutarch.Core.Validators (
  mkNFTMinting,
  alwaysFailScript,
  mkPermissionedMinting,
) where

import Plutarch.Core.FieldBinds (pletFieldsMinting)
import Plutarch.Core.List (pheadSingleton)
import Plutarch.Core.Utils (phasUTxO, ptxSignedByPkh)
import Plutarch.Core.ValidationLogic (pvalidateConditions)
import Plutarch.Core.Value (ptryLookupValue)
import Plutarch.Internal.Lift (pconstant)
import Plutarch.LedgerApi.V3 (PPubKeyHash, PScriptContext, PTxOutRef)
import Plutarch.Monadic qualified as P
import Plutarch.Prelude (ClosedTerm, PAsData, PData, PEq ((#==)), PUnit, perror,
                         pfield, pfromData, pfstBuiltin, plam, plet, pletFields,
                         psndBuiltin, type (:-->), (#))
import PlutusLedgerApi.V3 (TokenName)

-- | A one-shot minting policy that allows minting a single token with a given token name.
-- Arguments:
--   1. The token name to mint (Haskell level argument)
--   2. The UTxO reference of the protocol parameters UTxO.
mkNFTMinting :: TokenName -> ClosedTerm (PAsData PTxOutRef :--> PScriptContext :--> PUnit)
mkNFTMinting tn = plam $ \oref ctx -> P.do
  ctxF <- pletFields @'["txInfo", "scriptInfo"] ctx
  infoF <- pletFields @'["inputs", "mint"] ctxF.txInfo
  scriptInfoF <- pletFieldsMinting ctxF.scriptInfo
  let ownCS = scriptInfoF._0
  mintedValue <- plet $ pfromData infoF.mint
  let ownTkPairs = ptryLookupValue # ownCS # mintedValue
  -- Enforce that only a single token name is minted for this policy
  ownTkPair <- plet (pheadSingleton # ownTkPairs)
  ownTokenName <- plet (pfstBuiltin # ownTkPair)
  ownNumMinted <- plet (psndBuiltin # ownTkPair)
  pvalidateConditions
    [ ownTokenName #== pconstant tn
    , ownNumMinted #== pconstant 1
    , phasUTxO # oref # infoF.inputs
    ]

-- | Permissioned Minting Policy
-- This minting policy checks for a given permissioned credential in the signatories of the transaction.
-- It allows minting of any number of tokens with any token name so long as the credential authorizes the transaction.
-- Arguments:
--   1. Arbitrary BuiltinData used to provide a nonce to the script to allow the caller to create multiple
--      instances with different script hashes.
--   2. The permissioned credential that must be present in the signatories of the transaction.
mkPermissionedMinting :: ClosedTerm (PData :--> PAsData PPubKeyHash :--> PScriptContext :--> PUnit)
mkPermissionedMinting = plam $ \_ permissionedCred ctx ->
  pvalidateConditions
    [ ptxSignedByPkh # permissionedCred # (pfield @"signatories" # (pfield @"txInfo" # ctx))
    ]

-- | A nonced always fails script
-- The parameter is used to modify the script hash.
-- This is where the protocol parameters UTxO should reside.
-- Argument:
--  1. Arbitrary BuiltinData used to provide a nonce to the script to allow the caller to create multiple
--     instances with different script hashes.
alwaysFailScript :: ClosedTerm (PData :--> PScriptContext :--> PUnit)
alwaysFailScript = plam $ \_ _ctx -> perror
