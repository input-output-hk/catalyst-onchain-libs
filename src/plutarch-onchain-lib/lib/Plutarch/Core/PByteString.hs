{-|
Module      : Plutarch.Core.ByteString
Description : Plutarch functions for bytestring manipulation
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}

module Plutarch.Core.PByteString (
  pisPrefixOf,
  pisPrefixedWith,
  ptakeBS,
  pdropBS,
) where

import Plutarch.LedgerApi.Value (PTokenName)
import Plutarch.Prelude (PBool, PByteString, PEq ((#==)), PInteger, Term,
                         phoistAcyclic, plam, plengthBS, psliceBS, pto,
                         type (:-->), (#))

-- | Checks if a tokenName is prefixed by a certain ByteString
pisPrefixedWith :: forall s . Term s (PTokenName :--> PByteString :--> PBool)
pisPrefixedWith = plam $ \tn prefix ->
  pisPrefixOf # prefix # pto tn

-- | Checks if the first ByteString is a prefix of the second
pisPrefixOf :: forall s . Term s (PByteString :--> PByteString :--> PBool)
pisPrefixOf = plam $ \prefix src ->
  let prefixLength = plengthBS # prefix
      prefix' = psliceBS # 0 # prefixLength # src
   in prefix' #== prefix

-- | Take the first n bytes of a ByteString
ptakeBS :: Term s (PInteger :--> PByteString :--> PByteString)
ptakeBS = phoistAcyclic $ plam $ \n bs ->
  psliceBS # 0 # n # bs

-- | Drop the first n bytes of a ByteString
pdropBS :: Term s (PInteger :--> PByteString :--> PByteString)
pdropBS = phoistAcyclic $ plam $ \n bs ->
  psliceBS # n # (plengthBS # bs - n) # bs
