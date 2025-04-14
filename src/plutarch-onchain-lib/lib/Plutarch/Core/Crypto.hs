{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-|
Module      : Plutarch.Core.Crypto
Description : Plutarch functions for working with cryptographic values
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}
module Plutarch.Core.Crypto(
  pcardanoPubKeyToPubKeyHash,
  pethereumPubKeyToPubKeyHash,
  pcompressPublicKey,
  scriptHashV3,
  papplyHashedParameterV3
) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Short (fromShort)
import Data.Word (Word8)
import Plutarch.Builtin.ByteString (pintegerToByteString, pmostSignificantFirst)
import Plutarch.Builtin.Crypto (pblake2b_224, pkeccak_256)
import Plutarch.Core.Internal.Builtins (pindexBS')
import Plutarch.Core.PByteString (pdropBS, ptakeBS)
import Plutarch.Evaluate (unsafeEvalTerm)
import Plutarch.Internal.Term (Config (NoTracing))
import Plutarch.Prelude (ClosedTerm, PByteString, PEq ((#==)), PInteger, Term,
                         pconstant, phexByteStr, phoistAcyclic, pif, plam,
                         plengthBS, plet, pmod, type (:-->), (#))
import Plutarch.Script (Script (unScript))
import PlutusCore.Crypto.Hash qualified as Hash
import PlutusLedgerApi.Common (serialiseUPLC)

scriptHashV3 :: Script -> ByteString
scriptHashV3 = hashScriptWithPrefix 0x3

hashScriptWithPrefix :: Word8 -> Script -> ByteString
hashScriptWithPrefix prefix scr =
  Hash.blake2b_224
    $ BS.singleton prefix <> (fromShort . serialiseUPLC . unScript $ scr)

-- | Compute the hash of a public key (Cardano format)
-- The public key hash is the blake2b-224 hash of the public key.
pcardanoPubKeyToPubKeyHash :: Term s (PByteString :--> PByteString)
pcardanoPubKeyToPubKeyHash = phoistAcyclic $ plam $ \pubKey -> pblake2b_224 # pubKey

-- | Compute the hash of a public key (Ethereum format)
-- The public key hash is the keccak-256 hash of the last 20 bytes of the full public key.
pethereumPubKeyToPubKeyHash :: Term s (PByteString :--> PByteString)
pethereumPubKeyToPubKeyHash = phoistAcyclic $ plam $ \pubKey ->
  plet (pkeccak_256 # pubKey) $ \fullHash ->
    pdropBS # (plengthBS # fullHash - 20) # fullHash

-- | Compute the compressed form of a public key (Ethereum)
-- The compressed public key is the x-coordinate of the public key with a prefix byte.
-- The prefix byte is 0x02 if the y-coordinate is even, 0x03 if the y-coordinate is odd.
pcompressPublicKey :: Term s PByteString -> Term s PByteString
pcompressPublicKey pubKey =
  plet (ptakeBS # 32 # pubKey) $ \xCoordinate ->
    pif
      (peven yCoordinate)
      (pconstant "\x02" <> xCoordinate)
      (pconstant "\x03" <> xCoordinate)
  where
    yCoordinate = pdropBS # 32 # pubKey
    peven bs = (pmod # (pindexBS' # bs # 31) # 2) #== 0

-- | Given the CBOR-hex prefix of a parameterized Plutus script and a hashed parameter,
-- returns the hash of the full CBOR-hex representation after the parameter is applied.
--
-- This is useful for the "on-chain parameter validation" design pattern.
--
-- Suppose you have a Plutus script that accepts a parameter, and you deploy multiple
-- instances of it with different parameters. This function allows you to compute the
-- script hash of an instance — given the common prefix (up to the parameter) and the
-- hash of the specific parameter.
--
-- This is useful for verifying whether a known script hash corresponds to a specific
-- instantiation of a parameterized contract. You compute the expected hash using this
-- function and compare it to the one you want to validate. If they match, you know
-- the script is indeed the original contract with the given parameter applied.
--
-- This assumes the underlying script is PlutusV3.
papplyHashedParameterV3 :: forall s.
  Term s PByteString
  -> Term s PByteString
  -> Term s PByteString
papplyHashedParameterV3 prefix hashedParam =
  pblake2b_224 # (scriptHeader <> postfix)
  where
    postfix :: ClosedTerm PByteString
    postfix = phexByteStr "0001"

    versionHeader :: Term s PByteString
    versionHeader = unsafeEvalTerm NoTracing (pintegerToByteString # pmostSignificantFirst # 1 # plutusVersion)

    plutusVersion :: ClosedTerm PInteger
    plutusVersion = pconstant 3

    scriptHeader :: Term s PByteString
    scriptHeader = versionHeader <> prefix <> hashedParam

