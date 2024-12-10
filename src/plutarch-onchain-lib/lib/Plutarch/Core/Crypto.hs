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

import           Data.ByteString        (ByteString)
import qualified Data.ByteString        as BS
import           Data.ByteString.Short  (fromShort)
import           Data.Word              (Word8)
import           Plutarch               (Term, phoistAcyclic, plam, plet,
                                         type (:-->), (#))
import           Plutarch.Bool          (pif, (#==))
import           Plutarch.ByteString    (PByteString, pindexBS, plengthBS,
                                         psliceBS)
import           Plutarch.Crypto        (pblake2b_224, pkeccak_256)
import           Plutarch.Integer       (PInteger, pmod)
import           Plutarch.Lift          (pconstant)
import           Plutarch.Script        (Script (unScript))
import qualified PlutusCore.Crypto.Hash as Hash
import           PlutusLedgerApi.Common (serialiseUPLC)

scriptHashV3 :: Script -> ByteString
scriptHashV3 = hashScriptWithPrefix 0x3

hashScriptWithPrefix :: Word8 -> Script -> ByteString
hashScriptWithPrefix prefix scr =
  Hash.blake2b_224
    $ BS.singleton prefix <> (fromShort . serialiseUPLC . unScript $ scr)

pcardanoPubKeyToPubKeyHash :: Term s (PByteString :--> PByteString)
pcardanoPubKeyToPubKeyHash = phoistAcyclic $ plam $ \pubKey -> pblake2b_224 # pubKey

pethereumPubKeyToPubKeyHash :: Term s (PByteString :--> PByteString)
pethereumPubKeyToPubKeyHash = phoistAcyclic $ plam $ \pubKey ->
  plet (pkeccak_256 # pubKey) $ \fullHash ->
    pdropBS # (plengthBS # fullHash - 20) # fullHash

pcompressPublicKey :: Term s PByteString -> Term s PByteString
pcompressPublicKey pubKey =
  plet (ptakeBS # 32 # pubKey) $ \xCoordinate ->
    pif
      (peven yCoordinate)
      (pconstant "\x02" <> xCoordinate)
      (pconstant "\x03" <> xCoordinate)
  where
    yCoordinate = pdropBS # 32 # pubKey
    peven bs = (pmod # (pindexBS # bs # 31) # 2) #== 0

ptakeBS :: Term s (PInteger :--> PByteString :--> PByteString)
ptakeBS = phoistAcyclic $ plam $ \n bs ->
  psliceBS # 0 # n # bs

pdropBS :: Term s (PInteger :--> PByteString :--> PByteString)
pdropBS = phoistAcyclic $ plam $ \n bs ->
  psliceBS # n # (plengthBS # bs - n) # bs
