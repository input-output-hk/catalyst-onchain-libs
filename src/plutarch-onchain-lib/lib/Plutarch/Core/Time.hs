{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE QualifiedDo         #-}
module Plutarch.Core.Time (
  PPosixTimeRange,
  PPosixFiniteRange(..),
  ptoFiniteRange,
  pvalidityRangeStart,
  pvalidityRangeEnd,
  ptoCustomFiniteRangeH,
  pisFinite
) where

import GHC.Generics (Generic)
import Plutarch.Core.Data (pnonew)
import Plutarch.LedgerApi.V3 (PExtended (PFinite), PInterval (..),
                              PLowerBound (PLowerBound), PPosixTime (..),
                              PUpperBound (PUpperBound))
import Plutarch.Monadic qualified as P
import Plutarch.Prelude

type PPosixTimeRange = PInterval PPosixTime

data PPosixFiniteRange (s :: S) = PPosixFiniteRange
  { from :: Term s PPosixTime
  , to   :: Term s PPosixTime
  }
  deriving stock (Generic)
  deriving anyclass
    ( PlutusType
    )

instance DerivePlutusType PPosixFiniteRange where
  type DPTStrat _ = PlutusTypeScott

-- | Convert a 'PPosixTimeRange' to a 'PPosixFiniteRange'.
-- Errors if the provided time range is not finite.
ptoFiniteRange :: Term s (PPosixTimeRange :-->  PPosixFiniteRange)
ptoFiniteRange = phoistAcyclic $ plam $ \timeRange -> P.do
  timeRangeF <- pletFields @'["from", "to"] timeRange
  PLowerBound lb <- pmatch timeRangeF.from
  PFinite ((pfield @"_0" #) -> start) <- pmatch (pfield @"_0" # lb)
  PUpperBound ub <- pmatch timeRangeF.to
  PFinite ((pfield @"_0" #) -> end) <- pmatch (pfield @"_0" # ub)
  pcon $ PPosixFiniteRange { from = start, to = end }

-- | Get the start time of a 'PPosixTimeRange'.
-- Errors if the start time is not finite.
pvalidityRangeStart :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeStart = phoistAcyclic $ plam $ \timeRange -> P.do
  PInterval ((pfield @"from" #) -> startTime) <- pmatch timeRange
  PLowerBound lb <- pmatch startTime
  PFinite ((pfield @"_0" #) -> posixTime) <- pmatch (pfield @"_0" # lb)
  pmatch posixTime $ \(PPosixTime pt) -> pmatch pt $ \(PDataNewtype t) -> t

-- | Get the end time of a 'PPosixTimeRange'.
-- Errors if the end time is not finite.
pvalidityRangeEnd :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeEnd = phoistAcyclic $ plam $ \timeRange -> P.do
  PInterval ((pfield @"to" #) -> to_) <- pmatch timeRange
  PUpperBound ub <- pmatch to_
  PFinite ((pfield @"_0" #) -> posixTime) <- pmatch (pfield @"_0" # ub)
  pmatch posixTime $ \(PPosixTime pt) -> pmatch pt $ \(PDataNewtype t) -> t

-- | Extract the start and end times from a 'PPosixTimeRange' as Integers
-- and return them as a pair via CPS.
-- Errors if the start or end time is not finite.
ptoCustomFiniteRangeH :: Term s PPosixTimeRange -> TermCont @r s (Term s PInteger, Term s PInteger)
ptoCustomFiniteRangeH timeRange = do
  timeRangeF <- pletFieldsC @'["from", "to"] timeRange
  PLowerBound lb <- pmatchC timeRangeF.from
  PFinite ((pfield @"_0" #) -> start) <- pmatchC (pfield @"_0" # lb)
  PUpperBound ub <- pmatchC timeRangeF.to
  PFinite ((pfield @"_0" #) -> end) <- pmatchC (pfield @"_0" # ub)
  pure (pnonew $ pfromData start, pnonew $ pfromData end)

-- | Check if a 'PPosixTimeRange' is finite.
pisFinite :: Term s (PInterval PPosixTime :--> PBool)
pisFinite = plam $ \i ->
  let isFiniteFrom = pmatch (pfield @"_0" # (pfield @"from" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
      isFiniteTo = pmatch (pfield @"_0" # (pfield @"to" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
   in pand' # isFiniteFrom # isFiniteTo
