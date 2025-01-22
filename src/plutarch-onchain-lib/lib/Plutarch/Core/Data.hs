module Plutarch.Core.Data (
  pnonew,
  punnew
) where

import Plutarch.Prelude
import Plutarch.Internal.Term ( PType )

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