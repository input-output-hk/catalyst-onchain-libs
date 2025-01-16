{-# LANGUAGE CPP                  #-}
{-# LANGUAGE OverloadedRecordDot  #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QualifiedDo          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-|
Module      : Plutarch.Core.Utils
Description : Collection of plutarch utility functions
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}

module Plutarch.Core.Utils(
  pfail,
  pdebug,
  PTxOutH(..),
  pisRewarding,
  ptryFromInlineDatum,
  pfromPDatum,
  pnonew,
  punnew,
  ppair,
  passert,
  pcheck,
  pcountScriptInputs,
  pfoldl2,
  pelemAtWithRest',
  pmapIdxs,
  pmapFilter,
  tcexpectJust,
  paysToAddress,
  paysValueToAddress,
  paysAtleastValueToAddress,
  paysToCredential,
  pgetPubKeyHash,
  pmapMaybe,
  paysToPubKey,
  ptryOutputToAddress,
  ptryOwnOutput,
  ptryOwnInput,
  ptxSignedByPkh,
  (#-),
  pfindWithRest,
  pcountCS,
  pcountNonAdaCS,
  pfirstTokenName,
  ptryLookupValue,
  pfilterCSFromValue,
  phasUTxO,
  pvalueContains,
  pand'List,
  pcond,
  (#>=),
  (#>),
  (#/=),
  pisFinite,
  pmapAndConvertList,
  pintToByteString,
  punwrapPosixTime,
  pwrapPosixTime,
  pdivCeil,
  pisScriptCredential,
  pisPubKeyCredential,
  pvalidateConditions,
  pcountInputsFromCred,

) where

import qualified Data.Text                        as T
import           Plutarch.Prelude                 

import qualified Plutarch.LedgerApi.AssocMap      as AssocMap
import Plutarch.LedgerApi.V3
    ( KeyGuarantees(Sorted),
      PMap(..),
      PExtended(PFinite),
      PInterval,
      PMaybeData,
      PAddress,
      PCredential(..),
      PPubKeyHash,
      PDatum,
      PRedeemer,
      PScriptHash,
      PPosixTime(..),
      POutputDatum(POutputDatum),
      PTxOut,
      PScriptInfo,
      PScriptPurpose,
      PTxInInfo,
      PTxOutRef,
      AmountGuarantees(Positive),
      PCurrencySymbol,
      PTokenName,
      PValue(..) )            
import           Plutarch.LedgerApi.Value         (padaSymbol,
                                                   pvalueOf)
import qualified Plutarch.Monadic                 as P
                                         
import           Prelude
import           Plutarch.Internal.Term ( PType ) 

pfail ::
  forall (s :: S) a.
  Term s PString ->
  Term s a
#ifdef DEBUG
pfail = ptraceInfoError
#else
--- ^ Use this version for production. Smaller script size/exunits, but you won't get debugging messages
pfail _ = perror
#endif
--- ^ Use this version for testing. You will need modify node parameters to not blow up on TxSize/Exunits

pdebug ::
  forall (s :: S).
  Term s PString ->
  Term s PBool ->
  Term s PBool
#ifdef DEBUG
pdebug = ptraceInfoIfFalse
--- ^ Use this version for testing. You will need modify node parameters to not blow up on TxSize/Exunits
#else
pdebug _ b = b
--- ^ Use this version for production. Smaller script size/exunits, but you won't get debugging messages
#endif

data PTxOutH (s :: S) =
  PTxOutH
    { ptxOutAddress         :: Term s PAddress
    , ptxOutValue           :: Term s (PValue 'Sorted 'Positive)
    , ptxOutDatum           :: Term s POutputDatum
    , ptxOutReferenceScript :: Term s (PMaybeData PScriptHash)
    }

pisRewarding :: Term s (PAsData PScriptInfo) -> Term s PBool
pisRewarding term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 2


ptryFromInlineDatum :: forall (s :: S). Term s (POutputDatum :--> PDatum)
ptryFromInlineDatum = phoistAcyclic $
  plam $
    flip pmatch $ \case
      POutputDatum ((pfield @"outputDatum" #) -> datum) -> datum
      _ -> ptraceInfoError "not an inline datum"

-- | Parse a Datum into a specific structure (specified by the type argument)
-- and error if the datum does not decode to the expected structure.
-- Note: This function is very inefficient and should typically not be used, especially if the UTxO
-- in question has a state token that already enforces the correctness of the Datum structure.
-- For outputs typically you should prefer to construct the expected output datum and compare it against the
-- actual output datum thus entirely avoiding the need for decoding.
pfromPDatum ::
  forall (a :: PType) (s :: S).
  PTryFrom PData a =>
  Term s (PDatum :--> a)
pfromPDatum = phoistAcyclic $ plam $ flip ptryFrom fst . pto

-- Extract the inner type from a type which contains a `DataNewtype`
-- ex. PPosixTime -> PInteger
--     PPubKeyHash -> PByteString
pnonew :: forall {a :: PType} {b :: PType} {s :: S}.
                ((PInner a :: PType) ~ (PDataNewtype b :: PType), PIsData b) =>
                Term s a -> Term s b
pnonew nt = pmatch (pto nt) $ \(PDataNewtype bs) -> pfromData bs

-- Extract the inner type from a `PDataNewType`
-- ex. PDataNewtype PInteger -> PInteger
--     PDataNewtype PByteString -> PByteString
punnew :: forall {b :: PType} {s :: S}.
                PIsData b =>
                Term s (PDataNewtype b) -> Term s b
punnew nt = pmatch nt $ \(PDataNewtype bs) -> pfromData bs

ppair :: Term s a -> Term s b -> Term s (PPair a b)
ppair a b = pcon (PPair a b)

{- | If the input is True then continue otherwise throw an error message.
   Short trace is a sequence of first letters of long trace words.
-}
passert ::
  forall (s :: S) (a :: PType).
  T.Text -> -- long trace
  Term s PBool ->
  Term s a ->
  Term s a
passert longErrorMsg b inp = pif b inp $ ptraceInfoError (pconstant longErrorMsg)

-- | If the input is True then returns PJust otherwise PNothing
pcheck :: forall (s :: S) (a :: PType). Term s PBool -> Term s a -> Term s (PMaybe a)
pcheck b inp = pif b (pcon $ PJust inp) (pcon PNothing)

pcountScriptInputs :: Term s (PBuiltinList PTxInInfo :--> PInteger)
pcountScriptInputs =
  phoistAcyclic $
    let go :: Term s (PInteger :--> PBuiltinList PTxInInfo :--> PInteger)
        go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let cred = pfield @"credential" # (pfield @"address" # (pfield @"resolved" # x))
                   in pmatch cred $ \case
                        PScriptCredential _ -> self # (n + 1) # xs
                        _ -> self # n # xs
                )
                n
     in go # 0

pfoldl2 ::
  (PListLike listA, PListLike listB, PElemConstraint listA a, PElemConstraint listB b) =>
  Term s ((acc :--> a :--> b :--> acc) :--> acc :--> listA a :--> listB b :--> acc)
pfoldl2 =
  phoistAcyclic $ plam $ \func ->
    pfix #$ plam $ \self acc la lb ->
      pelimList
        ( \a as ->
            pelimList
              (\b bs -> self # (func # acc # a # b) # as # bs)
              perror
              lb
        )
        (pif (pnull # lb) acc perror)
        la

pelemAtWithRest' :: PListLike list => PElemConstraint list a => Term s (PInteger :--> list a :--> PPair a (list a))
pelemAtWithRest' = phoistAcyclic $
  pfix #$ plam $ \self n xs ->
    pif
      (n #== 0)
      (pcon $ PPair (phead # xs) (ptail # xs))
      (self # (n - 1) #$ ptail # xs)

pmapIdxs ::
  (PListLike listB, PElemConstraint listB b) =>
  Term s (PBuiltinList (PAsData PInteger) :--> listB b :--> listB b)
pmapIdxs =
  phoistAcyclic $
    pfix #$ plam $ \self la lb ->
      pelimList
        ( \a as -> P.do
            PPair foundEle xs <- pmatch $ pelemAtWithRest' # pfromData a # lb
            pcons # foundEle # (self # as # xs)
        )
        pnil
        la

pmapFilter ::
  (PIsListLike list a, PElemConstraint list b) => Term s ((b :--> PBool) :--> (a :--> b) :-->  list a :--> list b)
pmapFilter =
  phoistAcyclic $
    plam $ \predicate f ->
      precList
        ( \self x' xs -> plet (f # x') $ \x ->
            pif
              (predicate # x)
              (pcons # x # (self # xs))
              (self # xs)
        )
        (const pnil)

tcexpectJust :: forall r (a :: PType) (s :: S). Term s r -> Term s (PMaybe a) -> TermCont @r s (Term s a)
tcexpectJust escape ma = tcont $ \f -> pmatch ma $ \case
  PJust v -> f v
  PNothing -> escape

paysToAddress :: Term s (PAddress :--> PTxOut :--> PBool)
paysToAddress = phoistAcyclic $ plam $ \adr txOut -> adr #== (pfield @"address" # txOut)

paysValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pletFields @'["address", "value"] txOut $ \txoFields ->
      txoFields.address #== adr #&& txoFields.value #== val

paysAtleastValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysAtleastValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pletFields @'["address", "value"] txOut $ \txoFields ->
      txoFields.address #== adr #&& pvalueContains # val # txoFields.value

paysToCredential :: Term s (PScriptHash :--> PTxOut :--> PBool)
paysToCredential = phoistAcyclic $
  plam $ \valHash txOut ->
    let txOutCred = pfield @"credential" # (pfield @"address" # txOut)
     in pmatch txOutCred $ \case
          PScriptCredential txOutValHash -> (pfield @"_0" # txOutValHash) #== valHash
          PPubKeyCredential _ -> (pcon PFalse)


pgetPubKeyHash :: Term s PAddress -> Term s (PAsData PPubKeyHash)
pgetPubKeyHash addr =
  let cred = pfield @"credential" # addr
   in pmatch cred $ \case
        PScriptCredential _ -> perror
        PPubKeyCredential pkh' -> pfield @"_0" # pkh'

pmapMaybe ::
  forall (list :: PType -> PType) (a :: PType) (b :: PType).
  PListLike list =>
  PElemConstraint list a =>
  PElemConstraint list b =>
  ClosedTerm ((a :--> PMaybe b) :--> list a :--> list b)
pmapMaybe =
  phoistAcyclic $
    plam $ \func ->
      precList
        ( \self x xs ->
            pmatch (func # x) $ \case
              PJust y -> (pcons # y # (self # xs))
              PNothing -> (self # xs)
        )
        (const pnil)

paysToPubKey :: Term s (PPubKeyHash :--> PTxOut :--> PBool)
paysToPubKey = phoistAcyclic $
  plam $ \pkh txOut ->
    let txOutCred = pfield @"credential" # (pfield @"address" # txOut)
     in pmatch txOutCred $ \case
          PScriptCredential _ -> pconstant False
          PPubKeyCredential pkh' -> (pfield @"_0" # pkh') #== pkh

ptryOutputToAddress :: (PIsListLike list PTxOut) => Term s (list PTxOut :--> PAddress :--> PTxOut)
ptryOutputToAddress = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
              pif (target #== (pfield @"address" # txo)) txo (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOwnOutput :: Term s (PBuiltinList (PAsData PTxOut) :--> PScriptHash :--> PTxOut)
ptryOwnOutput = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
              pmatch (pfield @"credential" # (pfield @"address" # txo)) $ \case
                PPubKeyCredential _ -> (self # txos)
                PScriptCredential ((pfield @"_0" #) -> vh) ->
                  pif (target #== vh) (pfromData txo) (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOwnInput :: Term s (PBuiltinList (PAsData PTxInInfo) :--> PTxOutRef :--> PTxOut)
ptryOwnInput = phoistAcyclic $
  plam $ \inputs ownRef ->
    precList (\self x xs -> pletFields @'["outRef", "resolved"] x $ \txInFields -> pif (ownRef #== txInFields.outRef) txInFields.resolved (self # xs)) (const perror) # inputs

ptxSignedByPkh ::
  Term s (PAsData PPubKeyHash :--> PBuiltinList (PAsData PPubKeyHash) :--> PBool)
ptxSignedByPkh = pelem

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

pfirstTokenName ::
  forall
    (keys :: KeyGuarantees)
    (amounts :: AmountGuarantees)
    (s :: S).
  Term s (PValue keys amounts :--> PTokenName)
pfirstTokenName = phoistAcyclic $
  plam $ \val ->
    pmatch val $ \(PValue val') ->
      pmatch val' $ \(PMap csPairs) ->
        pmatch (pfromData (psndBuiltin # (phead # csPairs))) $ \(PMap tokens) ->
          pfromData $ pfstBuiltin # (phead # tokens)

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
  ClosedTerm
    ( PValue anyOrder anyAmount
        :--> PAsData PCurrencySymbol
        :--> PValue anyOrder anyAmount
    )
pfilterCSFromValue = phoistAcyclic $
  plam $ \value policyId ->
      let mapVal = pto (pto value)
          go = pfix #$ plam $ \self ys ->
                pelimList (\x xs -> pif (pfstBuiltin # x #== policyId) xs (pcons # x # (self # xs))) pnil ys
       in pcon (PValue $ pcon $ PMap $ go # mapVal)

{- | @phasUTxO # oref # inputs@
  ensures that in @inputs@ there is an input having @TxOutRef@ @oref@ .
-}
phasUTxO ::
  ClosedTerm
    ( PAsData PTxOutRef
        :--> PBuiltinList (PAsData PTxInInfo)
        :--> PBool
    )
phasUTxO = phoistAcyclic $
  plam $ \oref inInputs ->
    pany @PBuiltinList # plam (\input -> oref #== (pfield @"outRef" # input)) # inInputs

pvalueContains ::
  ClosedTerm
    ( PValue 'Sorted 'Positive
        :--> PValue 'Sorted 'Positive
        :--> PBool
    )
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

pand'List :: [Term s PBool] -> Term s PBool
pand'List ts' =
  case ts' of
    [] -> pconstant True
    ts -> foldl1 (\res x -> pand' # res # x) ts

-- pcond ::  [(Term s PBool, Term s a)] -> Term s a -> Term s a
-- pcond [] def                  = def
-- pcond ((cond, x) : conds) def = pif cond x $ pcond conds def

(#/=) :: (PEq t) => Term s t -> Term s t -> Term s PBool
a #/= b = pnot # (a #== b)
infix 4 #/=

pisFinite :: Term s (PInterval PPosixTime :--> PBool)
pisFinite = plam $ \i ->
  let isFiniteFrom = pmatch (pfield @"_0" # (pfield @"from" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
      isFiniteTo = pmatch (pfield @"_0" # (pfield @"to" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
   in pand' # isFiniteFrom # isFiniteTo

pmapAndConvertList :: (PIsListLike listA a, PIsListLike listB b) => Term s ((a :--> b) :--> listA a :--> listB b)
pmapAndConvertList = phoistAcyclic $
  plam $ \f ->
    pfix #$ plam $ \self xs -> pelimList (\y ys -> pcons # (f # y) # (self # ys)) pnil xs

pintToByteString :: Term s (PInteger :--> PByteString)
pintToByteString = phoistAcyclic $
  pfix #$ plam $ \self n ->
    plet
      (pquot # abs n # 10)
      ( \q ->
          plet (prem # abs n # 10) $ \r ->
            pif
              (q #== 0)
              (pshowDigit # r)
              ( plet (self # q) $ \prefix ->
                  prefix <> pshowDigit # r
              )
      )

pshowDigit :: Term s (PInteger :--> PByteString)
pshowDigit = phoistAcyclic $
  plam $ \digit ->
    pcond
      [ (digit #== 0, pconstant "0")
      , (digit #== 1, pconstant "1")
      , (digit #== 2, pconstant "2")
      , (digit #== 3, pconstant "3")
      , (digit #== 4, pconstant "4")
      , (digit #== 5, pconstant "5")
      , (digit #== 6, pconstant "6")
      , (digit #== 7, pconstant "7")
      , (digit #== 8, pconstant "8")
      , (digit #== 9, pconstant "9")
      ]
      perror

punwrapPosixTime :: Term s (PAsData PPosixTime) -> Term s PInteger
punwrapPosixTime pt = pmatch (pfromData pt) $ \(PPosixTime pt') -> pmatch pt' $ \(PDataNewtype t) -> pfromData t

pwrapPosixTime :: Term s PInteger -> Term s (PAsData PPosixTime)
pwrapPosixTime t = pdata $ pcon $ PPosixTime $ pcon $ PDataNewtype $ pdata t

pdivCeil :: Term s (PInteger :--> PInteger :--> PInteger)
pdivCeil = phoistAcyclic $
  plam $
    \x y -> 1 + pdiv # (x - 1) # y

pisScriptCredential :: Term s (PAsData PCredential) -> Term s PBool
pisScriptCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 1

pisPubKeyCredential :: Term s (PAsData PCredential) -> Term s PBool
pisPubKeyCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 0

-- | Strictly evaluates a list of boolean expressions.
-- If all the expressions evaluate to true, returns unit, otherwise throws an error.
pvalidateConditions :: [Term s PBool] -> Term s PUnit
pvalidateConditions conds =
  pif (pand'List conds)
      (pconstant ())
      perror

pcountInputsFromCred :: Term (s :: S) (PAsData PCredential :--> PBuiltinList (PAsData PTxInInfo) :--> PInteger)
pcountInputsFromCred =
  phoistAcyclic $ plam $ \cred txIns ->
    let go = pfix #$ plam $ \self n ->
              pelimList
                (\x xs ->
                  let inputCred = pfield @"credential" # (pfield @"address" # (pfield @"resolved" # x))
                   in pif (cred #== inputCred) (self # (n + 1) # xs) (self # n # xs)
                )
                n
     in go # 0 # txIns
