{-# LANGUAGE CPP        #-}
{-# LANGUAGE LambdaCase #-}

module Plutarch.Core.Trace (
  pfail,
  pdebug,
  pdebugWithPrefix,
  ptraceInfoWithPrefix,
  ptraceDebugWithPrefix,
  ptraceDebugWith,
  ptraceInfoWith,
) where

import Data.Kind (Type)
import Plutarch.Internal.Term (Config (NoTracing), pgetConfig)
#ifdef DEBUG
import Plutarch.Prelude (PBool, PShow, PString, S, Term, plam, pshow,
                         ptraceDebug, ptraceInfo, ptraceInfoError,
                         ptraceInfoIfFalse, (#), (:-->))
#else
import Plutarch.Prelude (PBool, PShow, PString, S, Term, perror, plam, pshow,
                         ptraceDebug, ptraceInfo, (#), (:-->))
#endif
import Prelude (($), (<>))

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

pdebugWithPrefix ::
  forall (a :: S -> Type) (s :: S).
#ifdef DEBUG
  PShow a =>
#endif
  Term s PString ->
  Term s a ->
  Term s a
#ifdef DEBUG
pdebugWithPrefix = ptraceInfoWithPrefix
--- ^ Use this version for testing. You will need modify node parameters to not blow up on TxSize/Exunits
#else
pdebugWithPrefix _ b = b
--- ^ Use this version for production. Smaller script size/exunits, but you won't get debugging messages
#endif

ptraceDebugWithPrefix ::
  forall (a :: S -> Type) (s :: S).
  PShow a =>
  Term s PString ->
  Term s a ->
  Term s a
ptraceDebugWithPrefix prefix =
  ptraceDebugWith (plam $ \x -> prefix <> pshow x)

ptraceInfoWithPrefix ::
  forall (a :: S -> Type) (s :: S).
  PShow a =>
  Term s PString ->
  Term s a ->
  Term s a
ptraceInfoWithPrefix prefix =
  ptraceInfoWith (plam $ \x -> prefix <> pshow x)

{- | Trace the given message at the debug level before evaluating the given
argument.
-}
ptraceDebugWith ::
  forall (a :: S -> Type) (s :: S).
  Term s (a :--> PString) ->
  Term s a ->
  Term s a
ptraceDebugWith f x = pgetConfig $ \case
  NoTracing -> x
  _ -> ptraceDebug (f # x) x

{- | Trace the given message at the debug level before evaluating the given
argument.
-}
ptraceInfoWith ::
  forall (a :: S -> Type) (s :: S).
  Term s (a :--> PString) ->
  Term s a ->
  Term s a
ptraceInfoWith f x = pgetConfig $ \case
  NoTracing -> x
  _ -> ptraceInfo (f # x) x
