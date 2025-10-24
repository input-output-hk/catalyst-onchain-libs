{-# LANGUAGE CPP                  #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QualifiedDo          #-}
{-# LANGUAGE UndecidableInstances #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-|
Module      : Plutarch.Core.Internal.Conditionals
Description : Collection of Plutarch conditionals
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}
module Plutarch.Core.Internal.Conditionals(pifInlined, pfixInlined) where

import Plutarch.Internal.Term (punsafeBuiltin, punsafeCoerce)
import Plutarch.Prelude
import PlutusCore qualified as PLC

-- | Conditional without hoisting the IfThenElse builtin.
-- Inlined variant of `pif`.
-- This results in lower exunits in exchange for a larger script size.
pifInlined :: Term s PBool -> Term s a -> Term s a -> Term s a
pifInlined cond ifT ifF =
  pforce $
    pforce (punsafeBuiltin PLC.IfThenElse) # cond # pdelay ifT # pdelay ifF

-- pfix but inlines the recursion point twice.
-- Inlined variant of `pfix`.
-- This results in lower exunits in exchange for a larger script size.
pfixInlined :: (Term s (a :--> b) -> Term s (a :--> b)) -> Term s (a :--> b)
pfixInlined f = plam (\r -> f (punsafeCoerce r # r)) # plam (\r -> f (punsafeCoerce r # r))

