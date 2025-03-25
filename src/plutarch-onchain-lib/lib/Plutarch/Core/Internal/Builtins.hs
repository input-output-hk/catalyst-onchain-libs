{-# LANGUAGE CPP                  #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QualifiedDo          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-|
Module      : Plutarch.Core.Internal.Builtins
Description : Collection of Plutarch builtins with raw types
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}
module Plutarch.Core.Internal.Builtins(pindexBS', pwriteBits', pcountSetBits', pconsBS', pmapData, ppairDataBuiltinRaw, pintegerToByteString') where

import Plutarch.Internal.Term (punsafeBuiltin)
import Plutarch.Prelude
import PlutusCore qualified as PLC

-- | Converts a 'PInteger' into a 'PByteString', given a desired endianness and target length.
--
-- The first argument is a 'PBool' indicating the endianness:
--   - 'True' for big-endian
--   - 'False' for little-endian
--
-- The second argument is the 'PInteger' to be converted.
--
-- The third argument is the target length of the resulting 'PByteString'.
--
-- Example usage:
--
-- @
-- pintegerToByteString' # True # 123456 # 8
-- @
pintegerToByteString' :: Term s (PBool :--> PInteger :--> PInteger :--> PByteString)
pintegerToByteString' = punsafeBuiltin PLC.IntegerToByteString

pcountSetBits' :: Term s (PByteString :--> PInteger)
pcountSetBits' = punsafeBuiltin PLC.CountSetBits

pwriteBits' :: forall (s :: S). Term s (PByteString :--> PBuiltinList PInteger :--> PBool :--> PByteString)
pwriteBits' = punsafeBuiltin PLC.WriteBits

pindexBS' :: Term s (PByteString :--> PInteger :--> PInteger)
pindexBS' = punsafeBuiltin PLC.IndexByteString

pconsBS' :: Term s (PInteger :--> PByteString :--> PByteString)
pconsBS' = punsafeBuiltin PLC.ConsByteString

-- Convert a BuiltinList of BuiltinPairs to a BuiltinMap
pmapData :: Term s (PBuiltinList (PBuiltinPair PData PData) :--> PData)
pmapData = punsafeBuiltin PLC.MapData

ppairDataBuiltinRaw :: Term s (PData :--> PData :--> PBuiltinPair PData PData)
ppairDataBuiltinRaw = punsafeBuiltin PLC.MkPairData
