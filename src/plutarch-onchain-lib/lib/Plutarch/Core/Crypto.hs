{-# LANGUAGE OverloadedStrings #-}
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
  scriptHashV3
) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Short (fromShort)
import Data.Word (Word8)
import Plutarch.Builtin.Crypto (pblake2b_224, pkeccak_256)
import Plutarch.Core.Internal.Builtins (pindexBS')
import Plutarch.Core.PByteString (pdropBS, ptakeBS)
import Plutarch.Prelude
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
