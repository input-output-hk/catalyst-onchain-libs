{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ImplicitPrelude       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedRecordDot   #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QualifiedDo           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
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
  pelemAtFast,
  pmustFind,
  pcanFind,
  pheadSingleton,
  pisSingleton,
  pnTails,
  ptails10,
  ptails20,
  ptails30,
  consAsData,
  pmkBuiltinList,
  pmkBuiltinListInteger,
  pmultiIntegerCons,
  pfindWithRest,
  psetBitInteger,
  pcheckIndex,
  pmapBuiltinListDataToInteger,
  pmapBuiltinListDataToIntegerFast,
) where

import Data.List (foldl')
import Generics.SOP (NP (..))
import Plutarch.Core.Internal.Builtins (pcountSetBits', pindexBS', pwriteBits')
import Plutarch.Internal.Term (PType)
import Plutarch.List hiding (pelemAt')
import Plutarch.Monadic qualified as P
import Plutarch.Prelude (ClosedTerm, PAsData, PBool (..), PBuiltinList (..),
                         PByteString, PData, PEq ((#==)), PInteger, PIsListLike,
                         PListLike (PElemConstraint, pcons, pelimList, phead, pnil, ptail),
                         PMultiplicativeSemigroup ((#*)), POrd ((#<), (#<=)),
                         PPair (..), S, Term, pasInt, pcon, pconcat, pcond,
                         pconsBS, pconstant, perror, pfix, pforgetData,
                         phexByteStr, phoistAcyclic, pif, plam, plet, pmatch,
                         pmod, precList, ptraceInfoError, type (:-->), (#$),
                         (#), (#>))
import Prelude

-- | Metaprogramming utility that translates to n applications of ptail
pnTails :: PIsListLike list a => Integer -> Term s (list a) -> Term s (list a)
pnTails n xs = foldl' (\acc _ -> ptail # acc) xs (replicate (fromIntegral n) ())

ptails10 :: PIsListLike list a => ClosedTerm (list a :--> list a)
ptails10 = phoistAcyclic $ plam (pnTails 10)

-- | Applies ptail 20 times to a list
ptails20 :: PIsListLike list a => ClosedTerm (list a :--> list a)
ptails20 = phoistAcyclic $ plam (\xs -> ptails10 # (ptails10 # xs))

-- | Applies ptail 30 times to a list
-- This has a lower script size than ptail inlined thirty times because it uses
-- hoisted functions which themselves invoke tail multiple times.
ptails30 :: PIsListLike list a => ClosedTerm (list a :--> list a)
ptails30 = phoistAcyclic $ plam (\xs -> ptails20 # (ptails10 # xs))

-- Get the head of the list if the list contains exactly one element, otherwise error.
pheadSingleton :: (PListLike list, PElemConstraint list a) => Term s (list a :--> a)
pheadSingleton = phoistAcyclic $
  plam $ \xs ->
    pelimList
      (pelimList (\_ _ -> ptraceInfoError "List contains more than one element."))
      (ptraceInfoError "List is empty.")
      xs

-- | Check if a list has exactly one element.
pisSingleton :: (PIsListLike list a) => Term s (list a) -> Term s PBool
pisSingleton = pelimList
      (\_ ys -> pelimList (\_ _ -> pconstant False) (pconstant True) ys)
      (pconstant False)

-- | Find the first element in a list that satisfies a predicate, and return it.
-- Errors if no element satisfies the predicate.
pmustFind :: PIsListLike l a => Term s ((a :--> PBool) :--> l a :--> a)
pmustFind =
  phoistAcyclic $ plam $ \f -> pfix #$ plam $ \self xs -> pelimList (\y ys -> pif (f # y) y (self # ys)) perror xs

-- | Check if a list contains an element that satisfies a predicate.
pcanFind :: PIsListLike l a => Term s ((a :--> PBool) :--> l a :--> PBool)
pcanFind =
  phoistAcyclic $ plam $ \f -> pfix #$ plam $ \self xs -> pelimList (\y ys -> pif (f # y) (pconstant True) (self # ys)) (pconstant False) xs

-- | Find the element at the given index in a list.
-- This function uses naive recursion and is not efficient for large lists.
pelemAt' :: PIsListLike l a => Term s (PInteger :--> l a :--> a)
pelemAt' = phoistAcyclic $
  pfix #$ plam $ \self n xs ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (n - 1) #$ ptail # xs)

-- | Find the element at the given index in a list.
-- Uses naive recursion and is inefficient for large lists.
-- However, the script size is smaller than the fast variant.
-- The arguments are flipped such that the list comes first to allow for partial application.
pelemAtFlipped' :: PIsListLike l a => Term s (l a :--> PInteger :--> a)
pelemAtFlipped' = phoistAcyclic $
  pfix #$ plam $ \self xs n ->
    pif
      (n #== 0)
      (phead # xs)
      (self # (ptail # xs) # (n - 1))

-- | Find the element at the given index in a list.
-- Uses an efficient implementation that handles multiple steps in each recursive call.
-- The arguments are flipped such that the list comes first to allow for partial application.
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

-- | Drop the first n elements of a list.
-- Uses naive recursion and is inefficient for large lists.
-- However, the script size is smaller than the fast variant.
pdropR :: forall (list :: PType -> PType) (a :: PType) (s :: S).
          PIsListLike list a =>
          Term s (PInteger :--> list a :--> list a)
pdropR = phoistAcyclic $
  let go :: Term (s2 :: S) (PInteger :--> list a :--> list a)
      go = pfix #$ plam $ \self n ys ->
            pif (n #== 0) ys (self # (n - 1) # (ptail # ys))
   in go

-- | Drop the first n elements of a list.
-- Uses an efficient implementation that handles a large number of steps in each recursive call.
-- The script size is larger than the naive variant, but ex-unit cost is significantly lower (it is more efficient).
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

emptyByteArray :: ClosedTerm PByteString
emptyByteArray = phexByteStr "0000000000000000000000000000000000000000000000000000000000000000"

-- | A list of powers of 2, represented as a PByteString.
single_byte_powers :: ClosedTerm PByteString
single_byte_powers = foldr (\x acc -> pconsBS # pconstant x # acc) mempty [1,2,4,8,16,32,64,128]

-- | Check if the given index is set in the given bitmask.
pcheckIndex :: Term s (PInteger :--> PInteger :--> PInteger)
pcheckIndex = phoistAcyclic $ plam $ \tagBits index -> P.do
  bit <- plet $ pow2_trick # index
  shifted_bit <- plet $ 2 * bit
  set_bit <- plet $ tagBits + bit
  pif (pmod # set_bit # shifted_bit #> pmod # tagBits # shifted_bit)
    set_bit
    perror

psetBitInteger :: Term s (PInteger :--> PInteger :--> PInteger)
psetBitInteger = phoistAcyclic $ plam $ \claimMask n -> P.do
  -- Check for a negative index
  pif (n #< 0)
    (ptraceInfoError "hi")
    $ P.do
      -- Compute 2^n (the nth bit)
      bit_n <- plet $ pow2_trick # n
      -- Compute the masked bits up to and including the nth bit
      bits0_n <- plet $ pmod # claimMask # (2 * bit_n)
      -- If nth bit is not set, add it to the claimMask
      pif (bits0_n #< bit_n)
        (claimMask + bit_n)
        -- Otherwise, throw an error
        (ptraceInfoError "hi")

-- | Efficiently compute 2^exponent using a trick that uses a lookup table.
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

-- | Compute 2^exponent
-- less efficient than pow2_trick, but has a smaller script size.
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

-- | Check if n bits are set in the given bytestring.
phasNSetBits :: Term s PInteger -> Term s PByteString -> Term s PBool
phasNSetBits n bs =
  let setBits = pcountSetBits' # bs
   in setBits #== n

-- | Check if a list consists of only unique elements.
-- Uses a bitmask to keep track of which elements have been seen.
-- However, the bitmask is implemented as an integer, and setting bits is done via
-- `pcheckIndex` (invoking pow2_trick).
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

-- | Recursively compute the length of a list.
pbuiltinListLength :: forall s a. (PElemConstraint PBuiltinList a) => Term s PInteger -> Term s (PBuiltinList a :--> PInteger)
pbuiltinListLength acc =
  (pfix #$ plam $ \self acc' l ->
    pelimList
      (\_ ys -> self # (acc' + 1) # ys)  -- cons case
      acc'                               -- nil case
      l
  )
  # acc

-- | Check that a list contains exactly n elements.
--  This is extremely efficient, as it counts a large number of elements in each recursive step.
--  The script size is larger than the naive variant, but the ex-unit cost is significantly lower.
pbuiltinListLengthFast :: forall (a :: PType) (s :: S). (PElemConstraint PBuiltinList a) => Term s (PInteger :--> PBuiltinList a :--> PInteger)
pbuiltinListLengthFast = phoistAcyclic $ plam $ \n elems ->
  let go :: Term (s2 :: S) (PInteger :--> PInteger :--> PBuiltinList a :--> PInteger)
      go = pfix #$ plam $ \self remainingExpected currentCount xs ->
             pcond
               [ (30 #<= remainingExpected, self # (remainingExpected - 30) # (currentCount + 30) # (ptails30 # xs))
               , (20 #<= remainingExpected, self # (remainingExpected - 20) # (currentCount + 20) # (ptails20 # xs))
               , (10 #<= remainingExpected, self # (remainingExpected - 10) # (currentCount + 10) # (ptails10 # xs))
               ]
               (currentCount + pbuiltinListLength 0 # xs)
   in go # n # 0 # elems

-- | Check if a list of data-encoded integers consists of only unique elements.
-- If so, returns the decoded list of integers. Otherwise, errors.
-- Uses a bitmask to keep track of which elements have been seen.
-- This should be used for the redeemer indexing design pattern because it avoids duplicate work and performs multiple necessary operations in a single pass.
-- Namely, it:
-- 1. Ensures the list consists of only unique elements.
-- 2. Ensures the length of the list is exactly n.
-- 3. Converts the list of data-encoded integers to a list of integers, which are returned and can be directly used with `pelemAtFast`.
puniqueSetDataEncoded :: Term s (PInteger :--> PBuiltinList (PAsData PInteger) :--> PBuiltinList PInteger)
puniqueSetDataEncoded = phoistAcyclic $ plam $ \n xs ->
  plet ((pmapBuiltinListDataToIntegerFast # n # xs)) \integerList ->
    let flagUniqueBits = pwriteBits' # emptyByteArray # integerList # pconstant True
    in pif (pcountSetBits' # flagUniqueBits #== n) integerList perror

-- | Check if a list consists of only unique elements.
-- Uses a bitmask to keep track of which elements have been seen.
-- Significantly more efficient than _pIsUnique.
pisUniqueSet :: Term s (PInteger :--> PBuiltinList PInteger :--> PBool)
pisUniqueSet = phoistAcyclic $ plam $ \n xs ->
  let flagUniqueBits = pwriteBits' # emptyByteArray # xs # pconstant True
  in (pcountSetBits' # flagUniqueBits #== (pbuiltinListLengthFast # n # xs))

-- | Check if a list has exactly n unique elements.
-- The entire list does not need to be unique, this will evaluate to true so long as
-- the list has n unique elements.
phasNUniqueElements :: Term s (PInteger :--> PBuiltinList PInteger :--> PBool)
phasNUniqueElements = phoistAcyclic $ plam $ \n xs ->
  let flagUniqueBits = pwriteBits' # emptyByteArray # xs # pconstant True
  in (pcountSetBits' # flagUniqueBits #== n)

-- | cons a data-encoded value of an arbitrary type to a BuiltinList of PData.
consAsData :: Term s (PAsData x) -> Term s (PBuiltinList PData) -> Term s (PBuiltinList PData)
consAsData x xs = pcon $ PCons (pforgetData x) xs

--- | Metaprogramming utility to construct a PBuiltinList from a list of PData.
pmkBuiltinList :: [Term s PData] -> Term s (PBuiltinList PData)
pmkBuiltinList = foldr go (pcon PNil)
  where
    go :: Term s PData -> Term s (PBuiltinList PData) -> Term s (PBuiltinList PData)
    go x xs = pcon $ PCons x xs

--- | Metaprogramming utility to construct a PBuiltinList from a list of PData.
pmkBuiltinListInteger :: [Term s PInteger] -> Term s (PBuiltinList PInteger)
pmkBuiltinListInteger = foldr go (pcon PNil)
  where
    go :: Term s PInteger -> Term s (PBuiltinList PInteger) -> Term s (PBuiltinList PInteger)
    go x xs = pcon $ PCons x xs

-- | Metaprogramming utility that prepends multiple integers to a list
-- pmultiIntegerCons [1, 2, 3] someList expands to: pcons # 1 #$ pcons # 2 #$ pcons # 3 #$ someList
-- >>> punsafeEvalTerm NoTracing (pmultiIntegerCons [1, 2, 3] (pnil))
pmultiIntegerCons :: [Term s PInteger] -> Term s (PBuiltinList PInteger :--> PBuiltinList PInteger)
pmultiIntegerCons xs = plam $ \ys -> go xs ys
  where
    go :: [Term s PInteger] -> Term s (PBuiltinList PInteger) -> Term s (PBuiltinList PInteger)
    go [] ys = ys
    go (x:rest) ys = pcons # x # (go rest ys)

-- | Find the first element in a list that satisfies a predicate, and return it along with the other elements
-- (the provided list with the element removed).
--
-- Errors if no element satisfies the predicate.
pfindWithRest ::
  forall (list :: PType -> PType) (a :: PType).
  PListLike list =>
  PElemConstraint list a =>
  ClosedTerm
    ( (a :--> PBool)
        :--> list a
        :--> PPair a (list a)
    )
pfindWithRest = phoistAcyclic $
  plam $ \f ys ->
    let mcons self x xs =
          pmatch (f # x) $ \case
            PTrue -> P.do
              acc <- plam
              pcon $ PPair x (pconcat # acc # xs)
            PFalse -> P.do
              acc <- plam
              self # xs #$ pcons # x # acc
        mnil = const (ptraceInfoError "Find")
     in precList mcons mnil # ys # pnil

-- | Convert PBuiltinList PData to PBuiltinList PInteger using efficient recursion unrolling
-- The first argument is the length of the input list.
pmapBuiltinListDataToIntegerFast :: Term s (PInteger :--> PBuiltinList PData :--> PBuiltinList PInteger)
pmapBuiltinListDataToIntegerFast = phoistAcyclic $ plam $ \n xs ->
  let go :: Term (s2 :: S) (PInteger :--> PBuiltinList PData :--> PBuiltinList PInteger)
      go = pfix #$ plam $ \self remainingExpected currentDataList ->
             pcond
               [ (20 #<= remainingExpected, (
                 pmatchList @20 @(PBuiltinList PInteger)
                  currentDataList
                  (\(entryOne
                     :* entryTwo
                     :* entryThree
                     :* entryFour
                     :* entryFive
                     :* entrySix
                     :* entrySeven
                     :* entryEight
                     :* entryNine
                     :* entryTen
                     :* entryEleven
                     :* entryTwelve
                     :* entryThirteen
                     :* entryFourteen
                     :* entryFifteen
                     :* entrySixteen
                     :* entrySeventeen
                     :* entryEighteen
                     :* entryNineteen
                     :* entryTwenty
                     :* Nil) rest ->
                    pmultiIntegerCons
                      [ pasInt # entryOne
                      , pasInt # entryTwo
                      , pasInt # entryThree
                      , pasInt # entryFour
                      , pasInt # entryFive
                      , pasInt # entrySix
                      , pasInt # entrySeven
                      , pasInt # entryEight
                      , pasInt # entryNine
                      , pasInt # entryTen
                      , pasInt # entryEleven
                      , pasInt # entryTwelve
                      , pasInt # entryThirteen
                      , pasInt # entryFourteen
                      , pasInt # entryFifteen
                      , pasInt # entrySixteen
                      , pasInt # entrySeventeen
                      , pasInt # entryEighteen
                      , pasInt # entryNineteen
                      , pasInt # entryTwenty
                      ] # (self # (remainingExpected - 20) # rest)
                    )
                  )
               )
               , (10 #<= remainingExpected, (
                   pmatchList @10 @(PBuiltinList PInteger)
                    currentDataList
                    (\(entryOne :* entryTwo :* entryThree :* entryFour :* entryFive :* entrySix :* entrySeven :* entryEight :* entryNine :* entryTen :* Nil) rest ->
                      pmultiIntegerCons
                        [ pasInt # entryOne
                        , pasInt # entryTwo
                        , pasInt # entryThree
                        , pasInt # entryFour
                        , pasInt # entryFive
                        , pasInt # entrySix
                        , pasInt # entrySeven
                        , pasInt # entryEight
                        , pasInt # entryNine
                        , pasInt # entryTen
                        ] # (self # (remainingExpected - 10) # rest)
                    )
                  ))
               ]
               (pmapBuiltinListDataToIntegerEnforceN remainingExpected # currentDataList)
   in go # n # xs


pmapBuiltinListDataToIntegerEnforceN :: forall s. Term s PInteger -> Term s (PBuiltinList PData :--> PBuiltinList PInteger)
pmapBuiltinListDataToIntegerEnforceN n =
  (pfix #$
    plam $ \self expectedRemaining inputDataList ->
      pelimList (\x xs -> pcons # (pasInt # x) # (self # (expectedRemaining - 1) # xs)) (pif (n #== 0) pnil perror) inputDataList
  ) # n

pmapBuiltinListDataToInteger :: Term s (PBuiltinList PData :--> PBuiltinList PInteger)
pmapBuiltinListDataToInteger =
  pfix #$
    plam $ \self inputDataList ->
      pelimList (\x xs -> pcons # (pasInt # x) # (self # xs)) pnil inputDataList

