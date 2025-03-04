module Plutarch.Core.Scripts(
  tryCompile,
  tryCompileTracingAndBinds,
  tryCompileNoTracing,
  scriptSize,
  serialiseScriptShort,
  serialisedScriptSize
  ) where

import Data.ByteString.Short qualified as SBS
import Plutarch.Internal.Term (ClosedTerm, Config (..), LogLevel (LogInfo),
                               Script, TracingMode (DoTracingAndBinds), compile)
import Plutarch.Internal.Term qualified as P
import Plutarch.Script qualified as P
import PlutusLedgerApi.Common qualified as P

tryCompile :: Config -> ClosedTerm a -> Script
tryCompile cfg x = case compile cfg x of
  Left e  -> error $ "Compilation failed: " <> show e
  Right s -> s

tryCompileTracingAndBinds :: ClosedTerm a -> Script
tryCompileTracingAndBinds = tryCompile (Tracing LogInfo DoTracingAndBinds)

tryCompileNoTracing :: ClosedTerm a -> Script
tryCompileNoTracing = tryCompile NoTracing

serialiseScriptShort :: P.Script -> SBS.ShortByteString
serialiseScriptShort = P.serialiseUPLC . P.unScript

scriptSize :: P.Script -> Int
scriptSize = serialisedScriptSize  . serialiseScriptShort

serialisedScriptSize :: P.SerialisedScript -> Int
serialisedScriptSize = SBS.length
