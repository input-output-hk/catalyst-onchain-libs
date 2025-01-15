{-# LANGUAGE CPP                  #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QualifiedDo          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}

module Plutarch.Core.FieldBinds where

import Plutarch.Prelude
import Plutarch.LedgerApi.V3
import Plutarch.DataRepr.Internal.Field
import Plutarch.Internal.Term


type PMintingScriptHRec (s :: S) =
  HRec
    '[ '("_0", Term s (PAsData PCurrencySymbol))
     ]

pletFieldsMinting :: forall {s :: S} {r :: PType}. Term s (PAsData PScriptInfo) -> (PMintingScriptHRec s -> Term s r) -> Term s r
pletFieldsMinting term = runTermCont $ do
  constrPair <- tcont $ plet $ pasConstr # pforgetData term
  fields <- tcont $ plet $ psndBuiltin # constrPair
  checkedFields <- tcont $ plet $ pif ((pfstBuiltin # constrPair) #== 0) fields perror
  let mintCS = punsafeCoerce @(PAsData PCurrencySymbol) $ phead # checkedFields
  tcont $ \f -> f $ HCons (Labeled @"_0" mintCS) HNil

type PSpendingScriptHRec (s :: S) =
  HRec
    '[ '("_0", Term s (PAsData PTxOutRef))
     , '("_1", Term s (PAsData (PMaybeData PDatum)))
     ]

-- Example usage:
--
-- @
-- pletFieldsSpending spendingScriptTerm $ \scriptInfoHRec ->
--   punsafeCoerce @_ @_ @PSignedObservation (pto scriptInfoHRec._1)
-- @
pletFieldsSpending :: forall {s :: S} {r :: PType}. Term s (PAsData PScriptInfo) -> (PSpendingScriptHRec s -> Term s r) -> Term s r
pletFieldsSpending term = runTermCont $ do
  constrPair <- tcont $ plet $ pasConstr # pforgetData term
  fields <- tcont $ plet $ psndBuiltin # constrPair
  checkedFields <- tcont $ plet $ pif ((pfstBuiltin # constrPair) #== 1) fields perror
  let outRef = punsafeCoerce @(PAsData PTxOutRef) $ phead # checkedFields
      datum = punsafeCoerce @(PAsData (PMaybeData PDatum)) $ phead # (ptail # checkedFields)
  tcont $ \f -> f $ HCons (Labeled @"_0" outRef) (HCons (Labeled @"_1" datum) HNil)

type PRewardingScriptHRec (s :: S) =
  HRec
    '[ '("_0", Term s (PAsData PCredential))
     ]

pletFieldsRewarding :: forall {s :: S} {r :: PType}. Term s (PAsData PScriptInfo) -> (PRewardingScriptHRec s -> Term s r) -> Term s r
pletFieldsRewarding term = runTermCont $ do
  constrPair <- tcont $ plet $ pasConstr # pforgetData term
  fields <- tcont $ plet $ psndBuiltin # constrPair
  checkedFields <- tcont $ plet $ pif ((pfstBuiltin # constrPair) #== 2) fields perror
  let withdrawingCred = punsafeCoerce @(PAsData PCredential) $ phead # checkedFields
  tcont $ \f -> f $ HCons (Labeled @"_0" withdrawingCred) HNil