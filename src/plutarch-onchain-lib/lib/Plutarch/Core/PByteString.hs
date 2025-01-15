{-|
Module      : Plutarch.Core.ByteString
Description : Plutarch functions for bytestring manipulation
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}

module Plutarch.Core.PByteString (
  pisPrefixOf
, pisPrefixedWith) where

import Plutarch.Prelude
import Plutarch.LedgerApi.Value ( PTokenName )

-- | Checks if a tokenName is prefixed by a certain ByteString
pisPrefixedWith :: ClosedTerm (PTokenName :--> PByteString :--> PBool)
pisPrefixedWith = plam $ \tn prefix ->
  pmatch (pto tn) $ \(PDataNewtype tnBS) -> pisPrefixOf # prefix # pfromData tnBS

-- | Checks if the first ByteString is a prefix of the second
pisPrefixOf :: ClosedTerm (PByteString :--> PByteString :--> PBool)
pisPrefixOf = plam $ \prefix src ->
  let prefixLength = plengthBS # prefix
      prefix' = psliceBS # 0 # prefixLength # src
   in prefix' #== prefix