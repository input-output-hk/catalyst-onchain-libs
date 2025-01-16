{-# LANGUAGE CPP                  #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QualifiedDo          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}

module Plutarch.Core.Value where

import Plutarch.Prelude
import Plutarch.LedgerApi.V3
import Plutarch.Core.PByteString(pisPrefixOf)
import Plutarch.LedgerApi.Value
import qualified Plutarch.LedgerApi.Value as Value
import qualified Plutarch.LedgerApi.AssocMap as AssocMap
import Plutarch.Internal.Term (punsafeCoerce, PType)
import Plutarch.Core.Internal.Builtins ( pmapData, ppairDataBuiltinRaw )
import Plutarch.Core.List (pheadSingleton)
import GHC.Generics (Generic)

{- | Finds the associated Currency symbols that contain token names prefixed with the ByteString.
-}
pfindCurrencySymbolsByTokenPrefix ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PByteString
        :--> PBuiltinList (PAsData PCurrencySymbol)
    )
pfindCurrencySymbolsByTokenPrefix = phoistAcyclic $
  plam $ \value prefix ->
    plet (pisPrefixOf # prefix) $ \prefixCheck ->
      let mapVal = pto (pto value)
          isPrefixed = pfilter # plam (\csPair ->
            pany # plam (\tkPair ->
              pmatch (pto (pfromData $ pfstBuiltin # tkPair)) $ \(PDataNewtype tkn) ->
                  prefixCheck # pfromData tkn
              ) # pto (pfromData (psndBuiltin # csPair))
            ) # mapVal
       in pmap # pfstBuiltin # isPrefixed

{- | Finds the associated Currency symbols that contain the given token
  name.
-}
pfindCurrencySymbolsByTokenName ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PTokenName
        :--> PBuiltinList (PAsData PCurrencySymbol)
    )
pfindCurrencySymbolsByTokenName = phoistAcyclic $
  plam $ \value tn ->
      let mapVal = pto (pto value)
          hasTn = pfilter # plam (\csPair -> pany # plam (\tk -> tn #== pfromData (pfstBuiltin # tk)) # pto (pfromData (psndBuiltin # csPair))) # mapVal
       in pmap # pfstBuiltin # hasTn

-- | Checks if a Currency Symbol is held within a Value
phasDataCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    (PAsData PCurrencySymbol :--> PValue anyOrder anyAmount :--> PBool)
phasDataCS = phoistAcyclic $
  plam $ \symbol value ->
    pany # plam (\tkPair -> (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

phasCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    (PValue anyOrder anyAmount :--> PCurrencySymbol :--> PBool)
phasCS = phoistAcyclic $
  plam $ \value symbol ->
    pany # plam (\tkPair -> pfromData (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

-- | Checks that a Value contains all the given CurrencySymbols.
pcontainsCurrencySymbols ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PBuiltinList (PAsData PCurrencySymbol)
        :--> PBool
    )
pcontainsCurrencySymbols = phoistAcyclic $
  plam $ \inValue symbols ->
    let value = pmap # pfstBuiltin #$ pto $ pto inValue
        containsCS = plam $ \cs -> pelem # cs # value
     in pall # containsCS # symbols

-- | Probably more effective than `plength . pflattenValue`
pcountOfUniqueTokens ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountOfUniqueTokens = phoistAcyclic $
  plam $ \val ->
    let tokensLength = plam (\pair -> pmatch (pfromData $ psndBuiltin # pair) $ \(PMap tokens) -> plength # tokens)
     in pmatch val $ \(PValue val') ->
          pmatch val' $ \(PMap csPairs) -> pfoldl # plam (\acc x -> acc + (tokensLength # x)) # 0 # csPairs

-- | Subtracts one Value from another
psubtractValue ::
  forall
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue 'Sorted amounts) ->
  Term s (PValue 'Sorted amounts) ->
  Term s (PValue 'Sorted 'NonZero)
a `psubtractValue` b = pnormalize #$ Value.punionResolvingCollisionsWith AssocMap.NonCommutative # plam (-) # a # b

-- | Constructs a singleton `PValue` with the given currency symbol, token name, and amount.
--
-- @param currencySymbol The currency symbol of the token.
-- @param tokenName The name of the token.
-- @param amount The amount of the token.
--
-- @return A singleton `PValue` containing the specified currency symbol, token name, and amount.
pvalueSingleton :: Term s (PAsData PCurrencySymbol) -> Term s (PAsData PTokenName) -> Term s (PAsData PInteger) -> Term s (PAsData (PValue 'Sorted 'Positive))
pvalueSingleton currencySymbol tokenName amount =
  let innerValue = pcons @PBuiltinList # (ppairDataBuiltin # tokenName # amount) # pnil
  in punsafeCoerce $ pmapData # (pcons @PBuiltinList # (ppairDataBuiltinRaw # pforgetData currencySymbol #$ pmapData # punsafeCoerce innerValue) # pnil)

-- Returns the amount of Ada contained in a Value
-- Errors if the Value contains tokens other than Ada
--
-- This function assumes that the first entry in the Value is Ada
-- The Cardano Ledger enforces that this invariant is maintained for all Values in the Script Context
-- So we are guaranteed that this is safe to use for any Value inside the Script Context
ponlyLovelaceValueOf :: Term s (PValue 'Sorted 'Positive) -> Term s PInteger
ponlyLovelaceValueOf val =
  let csPairs = pto $ pto val
      adaEntry = pheadSingleton # csPairs
  in pfromData (psndBuiltin #$ phead #$ pto $ pfromData $ psndBuiltin # adaEntry)

-- | Returns the amount of Ada contained in a Value
--
-- The Cardano Ledger enforces that this invariant is maintained for all Values in the Script Context
-- So we are guaranteed that this is safe to use for any Value inside the Script Context
plovelaceValueOf :: Term s (PValue 'Sorted 'Positive) -> Term s PInteger
plovelaceValueOf val =
  let csPairs = pto $ pto val
      adaEntry = phead # csPairs
  in pfromData (psndBuiltin #$ phead #$ pto $ pfromData $ psndBuiltin # adaEntry)

data PTriple (a :: PType) (b :: PType) (c :: PType) (s :: S)
  = PTriple (Term s a) (Term s b) (Term s c)
  deriving stock (Generic)
  deriving anyclass (PlutusType, PEq, PShow)

instance DerivePlutusType (PTriple a b c) where type DPTStrat _ = PlutusTypeScott

{- | Extract the token name and the amount of the given currency symbol.
Throws when the token name is not found or more than one token name is involved
Plutarch level function.
-}
ponlyAsset ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PTriple PCurrencySymbol PTokenName PInteger)
ponlyAsset = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      plet (pheadSingleton # pto val') $ \valuePair ->
        pmatch (pfromData (psndBuiltin # valuePair)) $ \(PMap tokens) ->
          plet (pheadSingleton # tokens) $ \tkPair ->
            pcon (PTriple (pfromData (pfstBuiltin # valuePair)) (pfromData (pfstBuiltin # tkPair)) (pfromData (psndBuiltin # tkPair)))

pvalueOfOneScott ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PCurrencySymbol
        :--> PValue keys amounts
        :--> PBool
    )
pvalueOfOneScott = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfromData (pfstBuiltin # x) #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # pto val'

pfirstTokenNameWithCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PAsData PCurrencySymbol :--> PValue keys amounts :--> PTokenName)
pfirstTokenNameWithCS = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData $ pfstBuiltin # (phead # tokens)
              )
              (self # xs)
        )
        (const perror)
        # pto val'

pvalueOfOne ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PBool
    )
pvalueOfOne = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # pto val'

psingletonOfCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PPair PTokenName PInteger
    )
psingletonOfCS = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  let tkPair = pheadSingleton # tokens
                   in pcon (PPair (pfromData (pfstBuiltin # tkPair)) (pfromData (psndBuiltin # tkPair)))
              )
              (self # xs)
        )
        (const perror)
        # pto val'
