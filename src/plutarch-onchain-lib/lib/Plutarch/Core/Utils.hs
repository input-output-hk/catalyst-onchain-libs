{-# LANGUAGE CPP                  #-}
{-# LANGUAGE NamedFieldPuns       #-}
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
  pmatchInlineDatum,
  ppair,
  passert,
  pcheck,
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
  ptryOutputToScriptHash,
  ptryOwnInput,
  ptxSignedByPkh,
  (#-),
  phasUTxO,
  pand'List,
  pcond,
  (#>=),
  (#>),
  (#/=),
  pmapAndConvertList,
  pintToByteString,
  pdivCeil,
  pisScriptCredential,
  pisPubKeyCredential,
  pisVotingScript,
  pisProposingScript,
  pisCertifyingScript,
  pisMintingScript,
  pisSpendingScript,
  pdeserializeCredential,
) where

import Data.Text qualified as T
import Plutarch.Prelude

import Plutarch.LedgerApi.V3
import Plutarch.Monadic qualified as P

import Plutarch.Core.Context (paddressCredential, ptxOutAddress,
                              ptxOutCredential)
import Plutarch.Core.List (pheadSingleton)
import Plutarch.Core.Value (pvalueContains)
import Plutarch.Internal.Term (PType)
import Prelude

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
    { ptxOutAddressH         :: Term s PAddress
    , ptxOutValueH           :: Term s (PValue 'Sorted 'Positive)
    , ptxOutDatumH           :: Term s POutputDatum
    , ptxOutReferenceScriptH :: Term s (PMaybeData PScriptHash)
    }

-- | Check the script info to determine if the script is being executed as a minting script.
pisMintingScript :: Term s (PAsData PScriptInfo) -> Term s PBool
pisMintingScript term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 0

-- | Check the script info to determine if the script is being executed as a spending script.
pisSpendingScript :: Term s (PAsData PScriptInfo) -> Term s PBool
pisSpendingScript term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 1

-- | Check the script info to determine if the script is being executed as a rewarding script.
pisRewarding :: Term s (PAsData PScriptInfo) -> Term s PBool
pisRewarding term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 2

-- | Check the script info to determine if the script is being executed as a certifying script.
pisCertifyingScript :: Term s (PAsData PScriptInfo) -> Term s PBool
pisCertifyingScript term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 3

-- | Check the script info to determine if the script is being executed as a voting script.
pisVotingScript :: Term s (PAsData PScriptInfo) -> Term s PBool
pisVotingScript term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 4

-- | Check the script info to determine if the script is being executed as a proposing script.
pisProposingScript :: Term s (PAsData PScriptInfo) -> Term s PBool
pisProposingScript term = (pfstBuiltin # (pasConstr # pforgetData term)) #== 5

pmatchInlineDatum :: forall (s :: S). Term s (POutputDatum :--> PDatum)
pmatchInlineDatum = phoistAcyclic $
  plam $
    flip pmatch $ \case
      POutputDatum pdatum -> pdatum
      _ -> ptraceInfoError "not an inline datum"

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
paysToAddress = phoistAcyclic $ plam $ \adr txOut -> adr #== ptxOutAddress txOut

paysValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pmatch txOut $ \(PTxOut {ptxOut'address, ptxOut'value}) ->
      ptxOut'address #== adr #&& pvalueContains # val # pfromData ptxOut'value

paysAtleastValueToAddress ::
  Term s (PValue 'Sorted 'Positive :--> PAddress :--> PTxOut :--> PBool)
paysAtleastValueToAddress = phoistAcyclic $
  plam $ \val adr txOut ->
    pmatch txOut $ \(PTxOut {ptxOut'address, ptxOut'value}) ->
      ptxOut'address #== adr #&& pvalueContains # val # pfromData ptxOut'value

paysToCredential :: Term s (PScriptHash :--> PTxOut :--> PBool)
paysToCredential = phoistAcyclic $
  plam $ \valHash txOut ->
    pmatch (ptxOutCredential txOut) $ \case
      PScriptCredential (pfromData -> txOutValHash) -> txOutValHash #== valHash
      PPubKeyCredential _ -> (pcon PFalse)

pgetPubKeyHash :: Term s PAddress -> Term s (PAsData PPubKeyHash)
pgetPubKeyHash addr =
  let cred = paddressCredential addr
   in pmatch cred $ \case
        PScriptCredential _ -> perror
        PPubKeyCredential pkh' -> pkh'

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

paysToPubKey :: Term s (PAsData PPubKeyHash :--> PTxOut :--> PBool)
paysToPubKey = phoistAcyclic $
  plam $ \pkh txOut ->
    let txOutCred = ptxOutCredential txOut
     in pmatch txOutCred $ \case
          PScriptCredential _ -> pconstant False
          PPubKeyCredential pkh' -> pkh' #== pkh

ptryOutputToAddress :: (PIsListLike list (PAsData PTxOut)) => Term s (list (PAsData PTxOut) :--> PAddress :--> PTxOut)
ptryOutputToAddress = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
             pmatch (pfromData txo) $ \case
              PTxOut {ptxOut'address} ->
                pif (target #== ptxOut'address) (pfromData txo) (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOutputToScriptHash :: Term s (PBuiltinList (PAsData PTxOut) :--> PAsData PScriptHash :--> PTxOut)
ptryOutputToScriptHash = phoistAcyclic $
  plam $ \outs target ->
    ( pfix #$ plam $ \self xs ->
        pelimList
          ( \txo txos ->
              pmatch (pfromData txo) $ \case
                PTxOut {ptxOut'address} ->
                  pmatch ptxOut'address $ \addr ->
                    pmatch (paddress'credential addr) $ \case
                      PScriptCredential vh ->
                        pif (target #== vh) (pfromData txo) (self # txos)
                      PPubKeyCredential _ -> (self # txos)
          )
          perror
          xs
    )
      # outs

ptryOwnInput :: Term s (PBuiltinList (PAsData PTxInInfo) :--> PTxOutRef :--> PTxOut)
ptryOwnInput = phoistAcyclic $
  plam $ \inputs ownRef ->
    precList (\self x xs ->
      pmatch (pfromData x) $ \(PTxInInfo {ptxInInfo'outRef, ptxInInfo'resolved}) ->
          pif (ownRef #== ptxInInfo'outRef) ptxInInfo'resolved (self # xs)
      ) (const perror) # inputs

ptxSignedByPkh ::
  Term s (PAsData PPubKeyHash :--> PBuiltinList (PAsData PPubKeyHash) :--> PBool)
ptxSignedByPkh = pelem

{- | @phasUTxO # oref # inputs@
  ensures that in @inputs@ there is an input having @TxOutRef@ @oref@ .
-}
phasUTxO ::
  ClosedTerm
    ( PTxOutRef
        :--> PBuiltinList (PAsData PTxInInfo)
        :--> PBool
    )
phasUTxO = phoistAcyclic $
  plam $ \oref inInputs ->
    pany @PBuiltinList # plam (\input ->
      pmatch (pfromData input) $ \ininfo ->
        oref #== ptxInInfo'outRef ininfo
      ) # inInputs

pand'List :: [Term s PBool] -> Term s PBool
pand'List ts' =
  case ts' of
    [] -> pconstant True
    ts -> foldl1 (\res x -> pand' # res # x) ts

-- Metaprogramming Example
-- This function was merged into Plutarch.
-- pcond ::  [(Term s PBool, Term s a)] -> Term s a -> Term s a
-- pcond [] def                  = def
-- pcond ((cond, x) : conds) def = pif cond x $ pcond conds def

(#/=) :: (PEq t) => Term s t -> Term s t -> Term s PBool
a #/= b = pnot # (a #== b)
infix 4 #/=

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

pdivCeil :: Term s (PInteger :--> PInteger :--> PInteger)
pdivCeil = phoistAcyclic $
  plam $
    \x y -> 1 + pdiv # (x - 1) # y

pisScriptCredential :: Term s (PAsData PCredential) -> Term s PBool
pisScriptCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 1

pisPubKeyCredential :: Term s (PAsData PCredential) -> Term s PBool
pisPubKeyCredential cred = (pfstBuiltin # (pasConstr # pforgetData cred)) #== 0

-- | Check if the provided data-encoded term has the expected builtin data representation of a credential.
pdeserializeCredential :: Term s (PAsData PCredential) -> Term s (PAsData PCredential)
pdeserializeCredential term =
  plet (pasConstr # pforgetData term) $ \constrPair ->
    plet (pfstBuiltin # constrPair) $ \constrIdx ->
      pif (plengthBS # (pasByteStr # (pheadSingleton # (psndBuiltin # constrPair))) #== 28)
          (
            pcond
              [ ( constrIdx #== 0 , term)
              , ( constrIdx #== 1 , term)
              ]
              (ptraceInfoError "Invalid credential")
          )
          perror
