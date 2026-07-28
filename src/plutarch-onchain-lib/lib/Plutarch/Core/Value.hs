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
  -- * Value representation
  -- $representation
  pvalueCsPairs,
  pledgerValueCsPairs,
  ptokenPairs,
  pmkSortedValue,
  pmkLedgerValue,

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
import Plutarch.LedgerApi.AssocMap qualified as AssocMap
import Plutarch.LedgerApi.V3 (PCurrencySymbol, PTokenName)
import Plutarch.LedgerApi.Value (PLedgerValue, PSortedValue, padaSymbol,
                                 padaSymbolData, pvalueOf)
import Plutarch.LedgerApi.Value qualified as Value
import Plutarch.Prelude (DeriveAsDataRec, PAsData, PBool, PBuiltinList,
                         PBuiltinPair, PByteString, PEq (..), PInteger,
                         PListLike (pcons, pelimList, phead, pnil, ptail),
                         POrd ((#<=)), S, Term, pall, pany, pcon, pconstant,
                         pdata, pelem, perror, pfilter, pfixHoisted, pfoldl,
                         pforgetData, pfromData, pfstBuiltin, phoistAcyclic,
                         pif, plam, plength, plet, pmap, pmatch,
                         ppairDataBuiltin, precList, psndBuiltin, pto,
                         type (:-->), (#$), (#))
import Plutarch.Repr.Data (DeriveAsDataRec (..))
import PlutusLedgerApi.V1 (TokenName (..))

{- $representation

plutarch-ledger-api 3.7.0 stopped exporting the constructors of the value and
map types, so their representation is reached with 'pto' rather than by pattern
matching, and each type sits at a different depth:

@
PAssocMap k v                    pto x1  -- the builtin pair list
PSortedMap / PUnsortedMap        pto x2
PSortedValue / PRawValue         pto x3
PLedgerValue / PMintValue        pto x4
@

The old @PValue@ reached its pair list in two, so every pre-3.7.0 @pto (pto v)@
is now short by one or two. A miscount typechecks in some positions and not
others -- @pto@ applied once to a 'AssocMap.PSortedMap' yields a
'AssocMap.PAssocMap', which anything list-polymorphic will happily accept.
These accessors exist so the depth is written down once, here, instead of at
every use site.
-}

{- | The currency-symbol / token-map pairs underlying a sorted value.

plutarch-ledger-api 3.7.0 replaced the phantom-tagged @PSortedValue@
with three distinct types and stopped exporting the constructors of
'PSortedValue' and 'PLedgerValue', so the representation is reached with 'pto'
rather than by pattern matching. It is also one level deeper than before:
'AssocMap.PSortedMap' wraps a 'AssocMap.PAssocMap', which wraps the builtin
list, where the old @PMap@ wrapped the list directly.
-}
pvalueCsPairs ::
  forall (s :: S).
  Term s PSortedValue ->
  Term s (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger))))
pvalueCsPairs v = pto (pto (pto v))

{- | The currency-symbol / token-map pairs underlying a ledger value.

'PLedgerValue' is a newtype over 'PSortedValue', so its representation sits one
'pto' deeper than 'pvalueCsPairs'. The same holds for
@Plutarch.LedgerApi.V3.MintValue.PMintValue@; coerce a mint to 'PSortedValue'
and use 'pvalueCsPairs' for that one.
-}
pledgerValueCsPairs ::
  forall (s :: S).
  Term s PLedgerValue ->
  Term s (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger))))
pledgerValueCsPairs = pvalueCsPairs . pto

-- | The token-name / quantity pairs of a sorted token map.
ptokenPairs ::
  forall (s :: S).
  Term s (AssocMap.PSortedMap PTokenName PInteger) ->
  Term s (PBuiltinList (PBuiltinPair (PAsData PTokenName) (PAsData PInteger)))
ptokenPairs m = pto (pto m)

{- | Rebuild a sorted value from its currency-pair list.

'PSortedValue' does not export its constructor, so this coerces. That is only
sound when the caller preserves the sortedness the type asserts. Every use in
this module derives the list from an ALREADY sorted value by dropping or
replacing the leading (ada) entry, neither of which can disturb the order of
the remainder -- ada's currency symbol is the empty bytestring, so it sorts
first and nothing can be reordered by removing it.
-}
pmkSortedValue ::
  forall (s :: S).
  Term s (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger)))) ->
  Term s PSortedValue
pmkSortedValue = punsafeCoerce

{- | Rebuild a ledger value from its currency-pair list.

Carries the soundness obligation of 'pmkSortedValue', and additionally the
non-negativity that 'PLedgerValue' asserts over 'PSortedValue': the caller must
supply quantities that are already known positive, which in practice means
deriving them from an existing ledger value rather than from arithmetic.
-}
pmkLedgerValue ::
  forall (s :: S).
  Term s (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger)))) ->
  Term s PLedgerValue
pmkLedgerValue = punsafeCoerce

adaTokenName :: TokenName
adaTokenName = TokenName ""

padaTokenData :: forall s . Term s (PAsData PTokenName)
padaTokenData = pconstant adaTokenName

{- | Finds the associated Currency symbols that contain token names prefixed with the ByteString.
-}
pfindCurrencySymbolsByTokenPrefix ::
  forall (s :: S).
  (Term s
    ( PSortedValue
        :--> PByteString
        :--> PBuiltinList (PAsData PCurrencySymbol)
    ))
pfindCurrencySymbolsByTokenPrefix = phoistAcyclic $
  plam $ \value prefix ->
    plet (pisPrefixOf # prefix) $ \prefixCheck ->
      let mapVal = pvalueCsPairs value
          isPrefixed = pfilter # plam (\csPair ->
              pany # plam (\tkPair ->
                prefixCheck # pto (pfromData $ pfstBuiltin # tkPair)
                ) # ptokenPairs (pfromData (psndBuiltin # csPair))
            ) # mapVal
       in pmap # pfstBuiltin # isPrefixed

{- | Finds the associated Currency symbols that contain the given token
  name.
-}
pfindCurrencySymbolsByTokenName ::
  forall (s :: S).
  ( Term s
    ( PSortedValue
        :--> PTokenName
        :--> PBuiltinList (PAsData PCurrencySymbol)
    ))
pfindCurrencySymbolsByTokenName = phoistAcyclic $
  plam $ \value tn ->
      let mapVal = pvalueCsPairs value
          hasTn = pfilter # plam (\csPair -> pany # plam (\tk -> tn #== pfromData (pfstBuiltin # tk)) # ptokenPairs (pfromData (psndBuiltin # csPair))) # mapVal
       in pmap # pfstBuiltin # hasTn

-- | Checks if a Currency Symbol is held within a Value
-- Arguments:
--   the currency symbol (must be data-encoded) to check for.
-- returns a boolean indicating whether the currency symbol is held within the value.
phasDataCS ::
  forall (s :: S).
  (Term s
    (PAsData PCurrencySymbol :--> PSortedValue :--> PBool))
phasDataCS = phoistAcyclic $
  plam $ \symbol value ->
    pany # plam (\tkPair -> (pfstBuiltin # tkPair) #== symbol) #$ pvalueCsPairs value

-- | Checks if a Currency Symbol is held within a Value
-- Arguments:
--   the currency symbol (must not be data-encoded) to check for.
-- returns a boolean indicating whether the currency symbol is held within the value.
phasCS ::
  forall (s :: S).
  (Term s
    (PSortedValue :--> PCurrencySymbol :--> PBool))
phasCS = phoistAcyclic $
  plam $ \value symbol ->
    pany # plam (\tkPair -> pfromData (pfstBuiltin # tkPair) #== symbol) #$ pvalueCsPairs value

-- | Checks that a Value contains all the given CurrencySymbols.
pcontainsCurrencySymbols ::
  forall (s :: S).
  (Term s
    ( PSortedValue
        :--> PBuiltinList (PAsData PCurrencySymbol)
        :--> PBool
    ))
pcontainsCurrencySymbols = phoistAcyclic $
  plam $ \inValue symbols ->
    let value = pmap # pfstBuiltin #$ pvalueCsPairs inValue
        containsCS = plam $ \cs -> pelem # cs # value
     in pall # containsCS # symbols

-- | Count the total number of unique tokens in the provided value.
-- This is useful for preventing the dust token attack without needing to be overly
-- restrictive on the content of a value (ie. enforce the value must only contain tokens that are known by the protocol)
pcountOfUniqueTokens ::
  forall (s :: S).
  Term s (PSortedValue :--> PInteger)
pcountOfUniqueTokens = phoistAcyclic $
  plam $ \val ->
    let tokensLength = plam (\pair -> plength # ptokenPairs (pfromData $ psndBuiltin # pair))
     in pfoldl # plam (\acc x -> acc + (tokensLength # x)) # 0 # pvalueCsPairs val

-- | Subtracts one Value from another
psubtractValue ::
  forall (s :: S).
  Term s (PSortedValue) ->
  Term s (PSortedValue) ->
  Term s (PSortedValue)
a `psubtractValue` b = Value.pnormalizeNoAdaNonZeroTokens #$ Value.punionWith # plam (-) # a # b

-- | Constructs a singleton `PValue` with the given currency symbol, token name, and amount.
-- Argumenmts:
--   The currency symbol of the token.
--   The name of the token.
--   The amount of the token.
--
-- @return A singleton `PValue` containing the specified currency symbol, token name, and amount.
pvalueSingleton :: Term s (PAsData PCurrencySymbol) -> Term s (PAsData PTokenName) -> Term s (PAsData PInteger) -> Term s (PAsData (PLedgerValue))
pvalueSingleton currencySymbol tokenName amount =
  let innerValue = pcons @PBuiltinList # (ppairDataBuiltin # tokenName # amount) # pnil
  in punsafeCoerce $ pmapData # (pcons @PBuiltinList # (ppairDataBuiltinRaw # pforgetData currencySymbol #$ pmapData # punsafeCoerce innerValue) # pnil)

-- Returns the amount of Ada contained in a Value
-- Errors if the Value contains tokens other than Ada
--
-- This function assumes that the first entry in the Value is Ada
-- The Cardano Ledger enforces that this invariant is maintained for all Values in the Script Context
-- So we are guaranteed that this is safe to use for any Value inside the Script Context
ponlyLovelaceValueOf :: Term s (PLedgerValue) -> Term s PInteger
ponlyLovelaceValueOf val =
  let csPairs = pvalueCsPairs (pto val)
      adaEntry = pheadSingleton # csPairs
  in pfromData (psndBuiltin #$ phead #$ ptokenPairs (pfromData (psndBuiltin # adaEntry)))

-- | Returns the amount of Ada contained in a Value
--
-- The Cardano Ledger enforces that this invariant is maintained for all Values in the Script Context
-- So we are guaranteed that this is safe to use for any Value inside the Script Context
plovelaceValueOfFast :: Term s (PLedgerValue) -> Term s PInteger
plovelaceValueOfFast val =
  let csPairs = pvalueCsPairs (pto val)
      adaEntry = phead # csPairs
  in pfromData (psndBuiltin #$ phead #$ ptokenPairs (pfromData (psndBuiltin # adaEntry)))

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
  forall (s :: S).
  Term s (PSortedValue :--> PTriple PCurrencySymbol PTokenName PInteger)
ponlyAsset = phoistAcyclic $
  plam $ \val ->
    ponlyAssetC val $ \(cs, tk, a) -> pcon $ PTriple cs tk a

{- | Same as `ponlyAsset` but returns the triple trough a haskell-level continuation.
-}
ponlyAssetC ::
  forall (s :: S) r.
  Term s (PSortedValue) -> ((Term s (PAsData PCurrencySymbol), Term s (PAsData PTokenName), Term s (PAsData PInteger)) -> Term s r) -> Term s r
ponlyAssetC value k =
    plet (pvalueCsPairs value) $ \val' ->
      plet (pheadSingleton # val') $ \valuePair ->
        plet (ptokenPairs (pfromData (psndBuiltin # valuePair))) $ \tokens ->
          plet (pheadSingleton # tokens) $ \tkPair ->
            k (pfstBuiltin # valuePair, pfstBuiltin # tkPair, psndBuiltin # tkPair)


-- | Check that the provided value contains exactly one token of the given currency symbol.
phasSingleTokenNoData ::
  forall (s :: S).
  Term
    s
    ( PCurrencySymbol
        :--> PSortedValue
        :--> PBool
    )
phasSingleTokenNoData = phoistAcyclic $
  plam $ \policyId val ->
    plet (pvalueCsPairs val) $ \val' ->
      precList
        ( \self x xs ->
            pif
              (pfromData (pfstBuiltin # x) #== policyId)
              ( plet (ptokenPairs (pfromData (psndBuiltin # x))) $ \tokens ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # val'

-- | Extract the first token name of the given currency symbol.
pfirstTokenNameWithCS ::
  forall (s :: S).
  Term s (PAsData PCurrencySymbol :--> PSortedValue :--> PTokenName)
pfirstTokenNameWithCS = phoistAcyclic $
  plam $ \policyId val ->
    plet (pvalueCsPairs val) $ \val' ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( plet (ptokenPairs (pfromData (psndBuiltin # x))) $ \tokens ->
                  pfromData $ pfstBuiltin # (phead # tokens)
              )
              (self # xs)
        )
        (const perror)
        # val'

-- | Check that a value contains exactly one token of a given currency symbol
-- and no other tokens with that currency symbol.
-- Errors if other tokens with the same currency symbol are present.
phasSingleToken ::
  forall (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PSortedValue
        :--> PBool
    )
phasSingleToken = phoistAcyclic $
  plam $ \policyId val ->
    plet (pvalueCsPairs val) $ \val' ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( plet (ptokenPairs (pfromData (psndBuiltin # x))) $ \tokens ->
                  pfromData (psndBuiltin # (pheadSingleton # tokens)) #== 1
              )
              (self # xs)
        )
        (const (pconstant False))
        # val'

-- | Check that there is exactly one token name with the given currency symbol in the provided value
-- return the token name and the quantity of the token.
ptrySingleTokenCS ::
  forall (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PSortedValue
        :--> PBuiltinPair (PAsData PTokenName) (PAsData PInteger)
    )
ptrySingleTokenCS = phoistAcyclic $
  plam $ \policyId val ->
    plet (pvalueCsPairs val) $ \val' ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( plet (ptokenPairs (pfromData (psndBuiltin # x))) $ \tokens ->
                  pheadSingleton # tokens
              )
              (self # xs)
        )
        (const perror)
        # val'

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
  forall (s :: S).
  Term
    s
    ( PAsData PCurrencySymbol
        :--> PSortedValue
        :--> PBuiltinList (PBuiltinPair (PAsData PTokenName) (PAsData PInteger))
    )
ptryLookupValue = phoistAcyclic $
  plam $ \policyId val ->
    plet (pvalueCsPairs val) $ \val' ->
      precList
        ( \self x xs ->
            pif
              (pfstBuiltin # x #== policyId)
              ( plet (ptokenPairs (pfromData (psndBuiltin # x))) $ \tokens ->
                  tokens
              )
              (self # xs)
        )
        (const perror)
        # val'

{- | Removes a currency symbol from a value
-}
pfilterCSFromValue ::
  forall (s :: S).
  (Term s
    ( PSortedValue
        :--> PAsData PCurrencySymbol
        :--> PSortedValue
    ))
pfilterCSFromValue = phoistAcyclic $
  plam $ \value policyId ->
      let mapVal = pvalueCsPairs value
          go = pfixHoisted #$ plam $ \self ys ->
                pelimList (\x xs -> pif (pfstBuiltin # x #== policyId) xs (pcons # x # (self # xs))) pnil ys
       in pmkSortedValue (go # mapVal)

-- | Check if a value contains another value
-- This function checks if the first value contains all the tokens of the second value
-- and the quantities of the tokens in the first value are greater than or equal to the quantities of the tokens in the second value.
pvalueContains ::
  (Term s
    ( PLedgerValue
        :--> PLedgerValue
        :--> PBool
    ))
pvalueContains = phoistAcyclic $
  plam $ \superset subset ->
    let forEachTN cs = plam $ \tnPair ->
          let tn = pfromData $ pfstBuiltin # tnPair
              amount = pfromData $ psndBuiltin # tnPair
           in amount #<= pvalueOf # pto superset # cs # tn
        forEachCS = plam $ \csPair ->
          let cs = pfromData $ pfstBuiltin # csPair
              tnMap = ptokenPairs (pfromData (psndBuiltin # csPair))
           in pall # forEachTN cs # tnMap
     in pall # forEachCS #$ pvalueCsPairs (pto subset)

-- TODO: Complete this function.
-- pvalueContainsFast ::
--   ClosedTerm
--     ( PLedgerValue
--         :--> PLedgerValue
--         :--> PBool
--     )
-- pvalueContainsFast = phoistAcyclic $ plam $ \superValue subValue ->
--   let go :: Term (s2 :: S) (PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger))) :--> PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger))) :--> PBool)
--       go = pfixHoisted #$ plam $ \self superSet subSet ->
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
  forall (s :: S).
  Term s (PSortedValue :--> PInteger)
pcountCS = phoistAcyclic $
  plam $ \val ->
    plength # pvalueCsPairs val

-- | Count the number of non-Ada currency symbols in a value.
pcountNonAdaCS ::
  forall (s :: S).
  Term s (PSortedValue :--> PInteger)
pcountNonAdaCS =
  phoistAcyclic $
    let go :: Term (s2 :: S) (PInteger :--> PBuiltinList (PBuiltinPair (PAsData PCurrencySymbol) (PAsData (AssocMap.PSortedMap PTokenName PInteger))) :--> PInteger)
        go = plet (pdata padaSymbol) $ \padaSymbolD ->
          pfixHoisted #$ plam $ \self n ->
            pelimList (\x xs -> pif (pfstBuiltin # x #== padaSymbolD) (self # n # xs) (self # (n + 1) # xs)) n
     in plam $ \val ->
          go # 0 # pvalueCsPairs val

-- | Strip Ada from a ledger value
-- This assumes that Ada is the first entry in the Value. If Ada is not the first entry, this function assumes the value does not
-- contain Ada and thus will just return the value as provided.
pstripAdaSafe ::
  forall (s :: S).
  Term s (PSortedValue :--> PSortedValue)
pstripAdaSafe = phoistAcyclic $
  plam $ \value ->
    let valMap = pvalueCsPairs value
        firstEntryCS = pfstBuiltin # (phead # valMap)
        nonAdaValueMapInner = ptail # valMap
     in pif (firstEntryCS #== padaSymbolData) (pmkSortedValue nonAdaValueMapInner) value

-- | Strip Ada from a ledger value
-- Importantly this function assumes that the Value is provided by the ledger (i.e. via the ScriptContext)
-- and thus the invariant that Ada is the first entry in the Value is maintained.
pstripAda ::
  forall (s :: S).
  Term s (PSortedValue :--> PSortedValue)
pstripAda = phoistAcyclic $
  plam $ \value ->
    let nonAdaValueMapInner = ptail # pvalueCsPairs value
    in pmkSortedValue nonAdaValueMapInner

-- | Update ada quantity in a value
-- Importantly this function assumes that the Value is provided by the ledger (i.e. via the ScriptContext)
-- and thus the invariant that Ada is the first entry in the Value is maintained.
pupdateAdaInValue ::
  forall (s :: S).
  Term s (PInteger :--> PSortedValue :--> PSortedValue)
pupdateAdaInValue = phoistAcyclic $
  plam $ \amnt value ->
    let innerAdaMap = pcons @PBuiltinList # (ppairDataBuiltin # padaTokenData # pdata amnt) # pnil
        adaEntry = punsafeCoerce $ ppairDataBuiltinRaw # pforgetData padaSymbolData #$ pmapData # punsafeCoerce innerAdaMap
        nonAdaValueMapInner = punsafeCoerce $ pcons # adaEntry # (ptail # pvalueCsPairs value)
    in pmkSortedValue nonAdaValueMapInner
