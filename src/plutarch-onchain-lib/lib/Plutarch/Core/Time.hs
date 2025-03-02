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
  pisFinite,
) where

import GHC.Generics (Generic)
import Plutarch.LedgerApi.V3 (PExtended (PFinite), PInterval (..),
                              PLowerBound (PLowerBound), PPosixTime (..),
                              PUpperBound (PUpperBound), unPPosixTime)
import Plutarch.Monadic qualified as P
import Plutarch.Prelude
import Plutarch.Unsafe (punsafeCoerce)
import Generics.SOP qualified as SOP

type PPosixTimeRange = PInterval PPosixTime

data PPosixFiniteRange (s :: S) = PPosixFiniteRange
  { from :: Term s PPosixTime
  , to   :: Term s PPosixTime
  }
  deriving stock (Generic)
  deriving anyclass
    ( SOP.Generic
    , PEq 
    , PShow 
    )
deriving via (PlutusType) via (DeriveAsSOPRec PPosixFiniteRange)


-- | Convert a 'PPosixTimeRange' to a 'PPosixFiniteRange'.
-- Errors if the provided time range is not finite.
ptoFiniteRange :: Term s (PPosixTimeRange :-->  PPosixFiniteRange)
ptoFiniteRange = phoistAcyclic $ plam $ \timeRange -> P.do
  PInterval lowerBound upperBound <- pmatch timeRange
  PLowerBound lb _ <- pmatch lowerBound
  PFinite start <- pmatch lb
  PUpperBound ub _ <- pmatch upperBound
  PFinite end <- pmatch ub
  pcon $ PPosixFiniteRange { from = pfromData start, to = pfromData end }

-- | Get the start time of a 'PPosixTimeRange'.
-- Errors if the start time is not finite.
pvalidityRangeStart :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeStart = phoistAcyclic $ plam $ \timeRange -> P.do
  interval <- pmatch timeRange
  let startTime = pinteral'from interval
  --PInterval ((pfield @"from" #) -> startTime) <- pmatch timeRange
  PLowerBound lb _ <- pmatch startTime
  PFinite posixTime <- pmatch lb
  punsafeCoerce $ pto posixTime

-- | Get the end time of a 'PPosixTimeRange'.
-- Errors if the end time is not finite.
pvalidityRangeEnd :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeEnd = phoistAcyclic $ plam $ \timeRange -> P.do
  interval <- pmatch timeRange
  let to_ = pinteral'to interval
  PUpperBound ub _ <- pmatch to_
  PFinite posixTime <- pmatch ub
  punsafeCoerce $ pto posixTime

-- | Extract the start and end times from a 'PPosixTimeRange' as Integers
-- and return them as a pair via CPS.
-- Errors if the start or end time is not finite.
ptoCustomFiniteRangeH :: Term s PPosixTimeRange -> TermCont @r s (Term s PInteger, Term s PInteger)
ptoCustomFiniteRangeH timeRange = do
  (PInterval from_ to_) <- pmatchC timeRange
  PLowerBound lb _ <- pmatchC from_
  PFinite (pfromData -> start) <- pmatchC lb
  PUpperBound ub _ <- pmatchC to_
  PFinite (pfromData -> end) <- pmatchC ub
  pure (unPPosixTime start, unPPosixTime end)

-- | Check if a 'PPosixTimeRange' is finite.
pisFinite :: Term s (PInterval PPosixTime :--> PBool)
pisFinite = plam $ \i ->
  pmatch i $ \(PInterval start' end') ->
    pmatch start' $ \(PLowerBound start _) ->
      pmatch end' $ \(PUpperBound end _) ->
        let isFiniteFrom = pmatch start $ \case
              PFinite _ -> pconstant True
              _ -> pconstant False
            isFiniteTo = pmatch end $ \case
              PFinite _ -> pconstant True
              _ -> pconstant False
        in pand' # isFiniteFrom # isFiniteTo
