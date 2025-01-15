{-# LANGUAGE QualifiedDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module Plutarch.Core.List (
  pdropFast,
  pdropR,
  pbuiltinListLengthFast,
  phasNSetBits,
  pisUniqueSet,
  _pIsUnique,
  phasNUniqueElements,
  emptyByteArray,
  pelemAt',
  pelemAtFlipped',
  pelemAtFast
) where

import           Plutarch.Prelude
import           Plutarch.Core.Utils         (ptails10, ptails20,
                                              ptails30)
import           Plutarch.Core.Internal.Builtins       (pcountSetBits', pwriteBits', pindexBS')                                            
import           Plutarch.Evaluate           (unsafeEvalTerm)
import           Plutarch.Internal.Term 
import qualified Plutarch.Monadic            as P
import           Prelude

pelemAt' :: PIsListLike l a => Term s (PInteger :--> l a :--> a)
pelemAt' = phoistAcyclic $
  pfix #$ plam $ \self n xs ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (n - 1) #$ ptail # xs)

pelemAtFlipped' :: PIsListLike l a => Term s (l a :--> PInteger :--> a)
pelemAtFlipped' = phoistAcyclic $
  pfix #$ plam $ \self xs n ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (ptail # xs) # (n - 1))

pelemAtFast :: (PIsListLike list a) => Term s (list a :--> PInteger :--> a)
pelemAtFast = phoistAcyclic $
  pfix #$ plam $ \self xs n ->
    pif
      (10 #< n)
      ( self
          # ( ptails10 # xs )
          # (n - 10)
      )
      ( pif
          (5 #< n)
          (self # (ptail #$ ptail #$ ptail #$ ptail #$ ptail # xs) # (n - 5))
          (pelemAtFlipped' # xs # n)
      )

pdropR :: forall (list :: PType -> PType) (a :: PType) (s :: S).
          PIsListLike list a =>
          Term s (PInteger :--> list a :--> list a)
pdropR = phoistAcyclic $
  let go :: Term (s2 :: S) (PInteger :--> list a :--> list a)
      go = pfix #$ plam $ \self n ys ->
            pif (n #== 0) ys (self # (n - 1) # (ptail # ys))
   in go

pdropFast :: PIsListLike PBuiltinList a => Term s (PInteger :--> PBuiltinList a :--> PBuiltinList a)
pdropFast = phoistAcyclic $
  let go = pfix #$ plam $ \self n ys ->
            pcond
              [ (30 #<= n, self # (n - 30) # (ptails30 # ys))
              , (20 #<= n, self # (n - 20) # (ptails20 # ys))
              , (10 #<= n, self # (n - 10) # (ptails10 # ys))
              ]
              (pdropR # n # ys)
   in go

_byteBools :: ClosedTerm (PBuiltinList PBool)
_byteBools = unsafeEvalTerm NoTracing $ foldr (\h t -> pcons # pconstant h # t) pnil (replicate 255 True)

emptyByteArray :: ClosedTerm PByteString
emptyByteArray = phexByteStr "0000000000000000000000000000000000000000000000000000000000000000"

single_byte_powers :: ClosedTerm PByteString
single_byte_powers = foldr (\x acc -> pconsBS # pconstant x # acc) mempty [1,2,4,8,16,32,64,128]
  --phexByteStr "0102040810204080"

pcheckIndex :: Term s (PInteger :--> PInteger :--> PInteger)
pcheckIndex = phoistAcyclic $ plam $ \tagBits index -> P.do
  bit <- plet $ pow2_trick # index
  shifted_bit <- plet $ 2 * bit
  set_bit <- plet $ tagBits + bit
  pif (pmod # set_bit # shifted_bit #> pmod # tagBits # shifted_bit)
    set_bit
    perror

pow2_trick :: Term s (PInteger :--> PInteger)
pow2_trick = plam $ \exponent' ->
  pcond
    [ (exponent' #< 8, pindexBS' # single_byte_powers # exponent')
    , (exponent' #< 16, 256 #* pindexBS' # single_byte_powers # (exponent' - 8))
    , (exponent' #< 24, 65536 #* pindexBS' # single_byte_powers # (exponent' - 16))
    , (exponent' #< 32, 16777216 #* pindexBS' # single_byte_powers # (exponent' - 24))
    , (exponent' #< 40, 4294967296 #* pindexBS' # single_byte_powers # (exponent' - 32))
    , (exponent' #< 48, 1099511627776 #* pindexBS' # single_byte_powers # (exponent' - 40))
    , (exponent' #< 56, 281474976710656 #* pindexBS' # single_byte_powers # (exponent' - 48))
    ]
    (281474976710656 #* ppow2 # (exponent' - 48))

ppow2 :: Term s (PInteger :--> PInteger)
ppow2 = phoistAcyclic $ pfix #$ plam $ \self e ->
  pif (e #< 8)
    (pif (e #< 0)
      0
      (pindexBS' # single_byte_powers # e)
    )
    (pif (e #< 32)
      (256 #* self # (e - 8))
      (4294967296 #* self # (e - 32))
    )

phasNSetBits :: Term s PInteger -> Term s PByteString -> Term s PBool
phasNSetBits n bs =
  let setBits = pcountSetBits' # bs
   in setBits #== n

-- exists to bench against pisUniqueSet
_pIsUnique :: Term s (PBuiltinList PInteger :--> PBool)
_pIsUnique = phoistAcyclic $ plam $ \list ->
  let go :: Term (s2 :: S) (PInteger :--> PBuiltinList PInteger :--> PBool)
      go = pfix #$ plam $ \self flag_bit xs ->
            pelimList
              (\y ys ->
                self # (pcheckIndex # flag_bit # y) # ys
              )
              (pconstant True)
              xs
  in go # 0 # list

pbuiltinListLength :: forall s a. (PElemConstraint PBuiltinList a) => Term s PInteger -> Term s (PBuiltinList a :--> PInteger)
pbuiltinListLength acc =
  (pfix #$ plam $ \self acc' l ->
    pelimList
      (\_ ys -> self # (acc' + 1) # ys)  -- cons case
      acc'                               -- nil case
      l
  )
  # acc

pbuiltinListLengthFast :: forall (a :: PType) (s :: S). (PElemConstraint PBuiltinList a) => Term s (PInteger :--> PBuiltinList a :--> PInteger)
pbuiltinListLengthFast = phoistAcyclic $ plam $ \n elems ->
  let go :: Term (s2 :: S) (PInteger :--> PInteger :--> PBuiltinList a :--> PInteger)
      go = pfix #$ plam $ \self remainingExpected currentCount xs ->
             pcond
               [ (30 #<= remainingExpected, self # (remainingExpected - 30) # (currentCount + 30) # (ptails30 # xs))
               , (20 #<= remainingExpected, self # (remainingExpected - 20) # (currentCount + 20) # (ptails20 # xs))
               , (10 #<= remainingExpected, self # (remainingExpected - 10) # (currentCount + 10) # (ptails10 # xs))
               ]
               (pbuiltinListLength 0 # xs)
   in go # n # 0 # elems

pisUniqueSet :: Term s (PInteger :--> PBuiltinList PInteger :--> PBool)
pisUniqueSet = phoistAcyclic $ plam $ \n xs ->
  let flagUniqueBits = pwriteBits' # emptyByteArray # xs # pconstant True
  in (pcountSetBits' # flagUniqueBits #== (pbuiltinListLengthFast # n # xs))

phasNUniqueElements :: Term s (PInteger :--> PBuiltinList PInteger :--> PBool)
phasNUniqueElements = phoistAcyclic $ plam $ \n xs ->
  let flagUniqueBits = pwriteBits' # emptyByteArray # xs # pconstant True
  in (pcountSetBits' # flagUniqueBits #== n)
