{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE QualifiedDo           #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Plutarch.Core.Value (
  pfindCurrencySymbolsByTokenPrefix,
  pfindCurrencySymbolsByTokenName,
  phasDataCS,
  phasCS,
  pcontainsCurrencySymbols,
  pcountOfUniqueTokens,
  psubtractValue,
  pvalueSingleton,
  ponlyLovelaceValueOf,
  plovelaceValueOfFast,
  ponlyAsset,
  ponlyAssetC,
  phasSingleTokenNoData,
  phasSingleToken,
  pfirstTokenNameWithCS,
  ptryLookupValue,
  pfilterCSFromValue,
  pvalueContains,
  pcountCS,
  pcountNonAdaCS,
  pstripAdaSafe,
  pstripAda,
  ptrySingleTokenCS,
  pupdateAdaInValue,

  PTriple (..),
) where

import Generics.SOP qualified as SOP
import GHC.Base (Type)
import GHC.Generics (Generic)
import Plutarch.Core.Internal.Builtins (pmapData, ppairDataBuiltinRaw)
import Plutarch.Core.List (pheadSingleton)
import Plutarch.Core.PByteString (pisPrefixOf)
import Plutarch.Internal.PlutusType (PlutusType)
import Plutarch.Internal.Term (punsafeCoerce)
import Plutarch.LedgerApi.V3 (AmountGuarantees (NonZero, Positive),
                              KeyGuarantees (Sorted), PCurrencySymbol,
                              PMap (..), PTokenName, PValue (..))
import Plutarch.LedgerApi.Value (padaSymbol, padaSymbolData, pnormalize,
                                 pvalueOf)
import Plutarch.LedgerApi.Value qualified as Value
import Plutarch.Prelude (DeriveAsDataRec, PAsData, PBool, PBuiltinList,
                         PBuiltinPair, PByteString, PEq (..), PInteger,
                         PListLike (pcons, pelimList, phead, pnil, ptail),
                         POrd ((#<=)), S, Term, pall, pany, pcon, pconstant,
                         pdata, pelem, perror, pfilter, pfix, pfoldl,
                         pforgetData, pfromData, pfstBuiltin, phoistAcyclic,
                         pif, plam, plength, plet, pmap, pmatch,
                         ppairDataBuiltin, precList, psndBuiltin, pto,
                         type (:-->), (#$), (#))
import Plutarch.Repr.Data (DeriveAsDataRec (..))
import PlutusLedgerApi.V1 (TokenName (..))

adaTokenName :: TokenName
adaTokenName = TokenName ""

padaTokenData :: forall s . Term s (PAsData PTokenName)
padaTokenData = pconstant adaTokenName

{- | Finds the associated Currency symbols that contain token names prefixed with the ByteString.
-}
pfindCurrencySymbolsByTokenPrefix ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  (forall s . Term s
    ( PValue anyOrder anyAmount
        :--> PByteString
        :--> PBuiltinList (PAsData PCurrencySymbol)
    ))
pfindCurrencySymbolsByTokenPrefix = phoistAcyclic $
  plam $ \value prefix ->
    plet (pisPrefixOf # prefix) $ \prefixCheck ->
      let mapVal = pto (pto value)
          isPrefixed = pfilter # plam (\csPair ->
              pany # plam (\tkPair ->
                prefixCheck # pto (pfromData $ pfstBuiltin # tkPair)
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
  ( forall s . Term s
    ( PValue anyOrder anyAmount
        :--> PTokenName
        :--> PBuiltinList (PAsData PCurrencySymbol)
    ))
pfindCurrencySymbolsByTokenName = phoistAcyclic $
  plam $ \value tn ->
      let mapVal = pto (pto value)
          hasTn = pfilter # plam (\csPair -> pany # plam (\tk -> tn #== pfromData (pfstBuiltin # tk)) # pto (pfromData (psndBuiltin # csPair))) # mapVal
       in pmap # pfstBuiltin # hasTn

-- | Checks if a Currency Symbol is held within a Value
-- Arguments:
--   the currency symbol (must be data-encoded) to check for.
-- returns a boolean indicating whether the currency symbol is held within the value.
phasDataCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  (forall s . Term s
    (PAsData PCurrencySymbol :--> PValue anyOrder anyAmount :--> PBool))
phasDataCS = phoistAcyclic $
  plam $ \symbol value ->
    pany # plam (\tkPair -> (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

-- | Checks if a Currency Symbol is held within a Value
-- Arguments:
--   the currency symbol (must not be data-encoded) to check for.
-- returns a boolean indicating whether the currency symbol is held within the value.
phasCS ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  (forall s . Term s
    (PValue anyOrder anyAmount :--> PCurrencySymbol :--> PBool))
phasCS = phoistAcyclic $
  plam $ \value symbol ->
    pany # plam (\tkPair -> pfromData (pfstBuiltin # tkPair) #== symbol) #$ pto (pto value)

-- | Checks that a Value contains all the given CurrencySymbols.
pcontainsCurrencySymbols ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  (forall s . Term s
    ( PValue anyOrder anyAmount
        :--> PBuiltinList (PAsData PCurrencySymbol)
        :--> PBool
    ))
pcontainsCurrencySymbols = phoistAcyclic $
  plam $ \inValue symbols ->
    let value = pmap # pfstBuiltin #$ pto $ pto inValue
        containsCS = plam $ \cs -> pelem # cs # value
     in pall # containsCS # symbols

-- | Count the total number of unique tokens in the provided value.
-- This is useful for preventing the dust token attack without needing to be overly
-- restrictive on the content of a value (ie. enforce the value must only contain tokens that are known by the protocol)
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
a `psubtractValue` b =  pnormalize #$ Value.punionWith # plam (-) # a # b

-- | Constructs a singleton `PValue` with the given currency symbol, token name, and amount.
-- Argumenmts:
--   The currency symbol of the token.
--   The name of the token.
--   The amount of the token.
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
plovelaceValueOfFast :: Term s (PValue 'Sorted 'Positive) -> Term s PInteger
plovelaceValueOfFast val =
  let csPairs = pto $ pto val
      adaEntry = phead # csPairs
  in pfromData (psndBuiltin #$ phead #$ pto $ pfromData $ psndBuiltin # adaEntry)

data PTriple (a :: S -> Type) (b :: S -> Type) (c :: S -> Type) (s :: S)
  = PTriple (Term s (PAsData a)) (Term s (PAsData b)) (Term s (PAsData c))
  deriving stock (Generic)
  deriving anyclass (SOP.Generic)
  deriving (PlutusType) via (DeriveAsDataRec (PTriple a b c))

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
    ponlyAssetC val $ \(cs, tk, a) -> pcon $ PTriple cs tk a

{- | Same as `ponlyAsset` but returns the triple trough a haskell-level continuation.
-}
ponlyAssetC ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S)
    r.
  Term s (PValue keys amounts) -> ((Term s (PAsData PCurrencySymbol), Term s (PAsData PTokenName), Term s (PAsData PInteger)) -> Term s r) -> Term s r
ponlyAssetC value k =
    pmatch value $ \(PValue val') ->
      plet (pheadSingleton # pto val') $ \valuePair ->
        pmatch (pfromData (psndBuiltin # valuePair)) $ \(PMap tokens) ->
          plet (pheadSingleton # tokens) $ \tkPair ->
            k (pfstBuiltin # valuePair, pfstBuiltin # tkPair, psndBuiltin # tkPair)


-- | Check that the provided value contains exactly one token of the given currency symbol.
phasSingleTokenNoData ::
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
phasSingleTokenNoData = phoistAcyclic $
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

-- | Extract the first token name of the given currency symbol.
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

-- | Check that a value contains exactly one token of a given currency symbol
-- and no other tokens with that currency symbol.
-- Errors if other tokens with the same currency symbol are present.
phasSingleToken ::
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
phasSingleToken = phoistAcyclic $
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

-- | Check that there is exactly one token name with the given currency symbol in the provided value
-- return the token name and the quantity of the token.
ptrySingleTokenCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PBuiltinPair (PAsData PTokenName) (PAsData PInteger)
    )
ptrySingleTokenCS = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  pheadSingleton # tokens
              )
              (self # xs)
        )
        (const perror)
        # pto val'

{- | Lookup the list of token-quantity pairs for a given currency symbol in a value.
     If the currency symbol is not found, the function will throw an error.

     This function takes a currency symbol and a value, and returns the list of token-quantity pairs
     associated with that currency symbol. The value is represented as a `PValue` which is a map of
     currency symbols to lists of token-quantity pairs. The function traverses this map to find the
     matching currency symbol and returns the associated list of token-quantity pairs.

     If the currency symbol is not found in the value, the function will throw an error using `perror`.

     Example usage:

     @
     let currencySymbol = ...
         value = ...
     in ptryLookupValue # currencySymbol # value
     @

     This will return the list of token-quantity pairs for the given currency symbol, or throw an error
     if the currency symbol is not found.

     Arguments:
     * `policyId` - The currency symbol to look up.
     * `val` - The value to search within.

     Returns:
     * A builtin list of token-quantity pairs associated with the given currency symbol.

-}
ptryLookupValue ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PValue keys amounts
        :--> PBuiltinList (PBuiltinPair (PAsData PTokenName) (PAsData PInteger))
    )
ptryLookupValue = phoistAcyclic $
  plam $ \policyId val ->
    pmatch val $ \(PValue val') ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( pmatch (pfromData (psndBuiltin # x)) $ \(PMap tokens) ->
                  tokens
              )
              (self # xs)
        )
        (const perror)
        # pto val'

{- | Removes a currency symbol from a value
-}
pfilterCSFromValue ::
  forall
    (anyOrder :: KeyGuarantees)
    (anyAmount :: AmountGuarantees).
  (forall s . Term s
    ( PValue anyOrder anyAmount
        :--> PAsData PCurrencySymbol
        :--> PValue anyOrder anyAmount
    ))
pfilterCSFromValue = phoistAcyclic $
  plam $ \value policyId ->
      let mapVal = pto (pto value)
          go = pfix #$ plam $ \self ys ->
                pelimList (\x xs -> pif (pfstBuiltin # x #== policyId) xs (pcons # x # (self # xs))) pnil ys
       in pcon (PValue $ pcon $ PMap $ go # mapVal)

-- | Check if a value contains another value
-- This function checks if the first value contains all the tokens of the second value
-- and the quantities of the tokens in the first value are greater than or equal to the quantities of the tokens in the second value.
pvalueContains ::
  (forall s . Term s
    ( PValue 'Sorted 'Positive
        :--> PValue 'Sorted 'Positive
        :--> PBool
    ))
pvalueContains = phoistAcyclic $
  plam $ \superset subset ->
    let forEachTN cs = plam $ \tnPair ->
          let tn = pfromData $ pfstBuiltin # tnPair
              amount = pfromData $ psndBuiltin # tnPair
           in amount #<= pvalueOf # superset # cs # tn
        forEachCS = plam $ \csPair ->
          let cs = pfromData $ pfstBuiltin # csPair
              tnMap = pto $ pfromData $ psndBuiltin # csPair
           in pall # forEachTN cs # tnMap
     in pall # forEachCS #$ pto $ pto subset

-- TODO: Complete this function.
-- pvalueContainsFast ::
--   ClosedTerm
--     ( PValue 'Sorted 'Positive
--         :--> PValue 'Sorted 'Positive
--         :--> PBool
--     )
-- pvalueContainsFast = phoistAcyclic $ plam $ \superValue subValue ->
--   let go :: Term (s2 :: S) (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (PMap keys PTokenName PInteger))) :--> PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (PMap keys PTokenName PInteger))) :--> PBool)
--       go = pfix #$ plam $ \self superSet subSet ->
--             pelimList (\superCSPair superCSPairs ->
--               pelimList (\subCSPair subCSPairs ->
--                 let superCS = pfromData $ pfstBuiltin # superCSPair
--                     subCS = pfromData $ pfstBuiltin # subCSPair
--                 in
--                   pif (superCS #< subCSPair)
--                       (self # superCSPairs # subSet)
--                       (
--                         pif (superCS #== subCS)
--                             ( pconstant True)
--                             (pconstant False)
--                       )

--               )
--               (pconstant True)
--               subSet
--              ) (pconstant False) superSet
--     innerVal :: Term _ (PMap Sorted PCurrencySymbol (PMap Sorted PTokenName PInteger))
--     innerVal = pto superValue
--     tokensMap :: Term
--                   _
--                   (PBuiltinList
--                     (PBuiltinPair
--                         (PAsData PCurrencySymbol)
--                         (PAsData (PMap Sorted PTokenName PInteger))))
--     tokensMap = pto innerVal
--  in go # tokensMap # pto (pto subValue)

-- | Count the number of currency symbols in a value.
pcountCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountCS = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      pmatch val' $ \(PMap csPairs) ->
        plength # csPairs

-- | Count the number of non-Ada currency symbols in a value.
pcountNonAdaCS ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PInteger)
pcountNonAdaCS =
  phoistAcyclic $
    let go :: Term (s2 :: S) (PInteger :--> PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (PMap keys PTokenName PInteger))) :--> PInteger)
        go = plet (pdata padaSymbol) $ \padaSymbolD ->
          pfix #$ plam $ \self n ->
            pelimList (\x xs -> pif (pfstBuiltin # x #== padaSymbolD) (self # n # xs) (self # (n + 1) # xs)) n
     in plam $ \val ->
          pmatch val $ \(PValue val') ->
            pmatch val' $ \(PMap csPairs) ->
              go # 0 # csPairs

-- | Strip Ada from a ledger value
-- This assumes that Ada is the first entry in the Value. If Ada is not the first entry, this function assumes the value does not
-- contain Ada and thus will just return the value as provided.
pstripAdaSafe ::
  forall
    (v :: AmountGuarantees)
    (s :: S).
  Term s (PValue 'Sorted v :--> PValue 'Sorted v)
pstripAdaSafe = phoistAcyclic $
  plam $ \value ->
    let valMap = pto (pto value)
        firstEntryCS = pfstBuiltin # (phead # valMap)
        nonAdaValueMapInner = ptail # valMap
     in pif (firstEntryCS #== padaSymbolData) (pcon (PValue $ pcon $ PMap nonAdaValueMapInner)) value

-- | Strip Ada from a ledger value
-- Importantly this function assumes that the Value is provided by the ledger (i.e. via the ScriptContext)
-- and thus the invariant that Ada is the first entry in the Value is maintained.
pstripAda ::
  forall (v :: AmountGuarantees) (s :: S).
  Term s (PValue 'Sorted v :--> PValue 'Sorted v)
pstripAda = phoistAcyclic $
  plam $ \value ->
    let nonAdaValueMapInner = ptail # pto (pto value)
    in pcon (PValue $ pcon $ PMap nonAdaValueMapInner)

-- | Update ada quantity in a value
-- Importantly this function assumes that the Value is provided by the ledger (i.e. via the ScriptContext)
-- and thus the invariant that Ada is the first entry in the Value is maintained.
pupdateAdaInValue ::
  forall (v :: AmountGuarantees) (s :: S).
  Term s (PInteger :--> PValue 'Sorted v :--> PValue 'Sorted v)
pupdateAdaInValue = phoistAcyclic $
  plam $ \amnt value ->
    let innerAdaMap = pcons @PBuiltinList # (ppairDataBuiltin # padaTokenData # pdata amnt) # pnil
        adaEntry = punsafeCoerce $ ppairDataBuiltinRaw # pforgetData padaSymbolData #$ pmapData # punsafeCoerce innerAdaMap
        nonAdaValueMapInner = punsafeCoerce $ pcons # adaEntry # (ptail # pto (pto value))
    in pcon (PValue $ pcon $ PMap nonAdaValueMapInner)
