{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE QualifiedDo         #-}
module Plutarch.Core.Time (
  PPosixTimeRange,
  PPosixFiniteRange(..),
  ptoFiniteRange,
  pvalidityRangeStart,
  pvalidityRangeEnd,
  ptoCustomFiniteRange,
  ptoCustomFiniteRangeH,
  pisFinite
) where

import GHC.Generics (Generic)
import Plutarch.Core.Data
import Plutarch.LedgerApi.V3
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

ptoFiniteRange :: Term s (PPosixTimeRange :-->  PPosixFiniteRange)
ptoFiniteRange = phoistAcyclic $ plam $ \timeRange -> P.do
  timeRangeF <- pletFields @'["from", "to"] timeRange
  PLowerBound lb <- pmatch timeRangeF.from
  PFinite ((pfield @"_0" #) -> start) <- pmatch (pfield @"_0" # lb)
  PUpperBound ub <- pmatch timeRangeF.to
  PFinite ((pfield @"_0" #) -> end) <- pmatch (pfield @"_0" # ub)
  pcon $ PPosixFiniteRange { from = start, to = end }

pvalidityRangeStart :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeStart = phoistAcyclic $ plam $ \timeRange -> P.do
  PInterval ((pfield @"from" #) -> startTime) <- pmatch timeRange
  PLowerBound lb <- pmatch startTime
  PFinite ((pfield @"_0" #) -> posixTime) <- pmatch (pfield @"_0" # lb)
  pmatch posixTime $ \(PPosixTime pt) -> pmatch pt $ \(PDataNewtype t) -> t

pvalidityRangeEnd :: Term s (PPosixTimeRange :--> PAsData PInteger)
pvalidityRangeEnd = phoistAcyclic $ plam $ \timeRange -> P.do
  PInterval ((pfield @"to" #) -> to_) <- pmatch timeRange
  PUpperBound ub <- pmatch to_
  PFinite ((pfield @"_0" #) -> posixTime) <- pmatch (pfield @"_0" # ub)
  pmatch posixTime $ \(PPosixTime pt) -> pmatch pt $ \(PDataNewtype t) -> t

ptoCustomFiniteRange :: Term s (PPosixTimeRange :--> PPosixFiniteRange)
ptoCustomFiniteRange = phoistAcyclic $ plam $ \timeRange -> P.do
  timeRangeF <- pletFields @'["from", "to"] timeRange
  PLowerBound lb <- pmatch timeRangeF.from
  PFinite ((pfield @"_0" #) -> start) <- pmatch (pfield @"_0" # lb)
  PUpperBound ub <- pmatch timeRangeF.to
  PFinite ((pfield @"_0" #) -> end) <- pmatch (pfield @"_0" # ub)
  pcon $ PPosixFiniteRange { from = start, to = end }

ptoCustomFiniteRangeH :: Term s PPosixTimeRange -> TermCont @r s (Term s PInteger, Term s PInteger)
ptoCustomFiniteRangeH timeRange = do
  timeRangeF <- pletFieldsC @'["from", "to"] timeRange
  PLowerBound lb <- pmatchC timeRangeF.from
  PFinite ((pfield @"_0" #) -> start) <- pmatchC (pfield @"_0" # lb)
  PUpperBound ub <- pmatchC timeRangeF.to
  PFinite ((pfield @"_0" #) -> end) <- pmatchC (pfield @"_0" # ub)
  pure (pnonew $ pfromData start, pnonew $ pfromData end)

pisFinite :: Term s (PInterval PPosixTime :--> PBool)
pisFinite = plam $ \i ->
  let isFiniteFrom = pmatch (pfield @"_0" # (pfield @"from" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
      isFiniteTo = pmatch (pfield @"_0" # (pfield @"to" # i)) $ \case
        PFinite _ -> pconstant True
        _ -> pconstant False
   in pand' # isFiniteFrom # isFiniteTo
