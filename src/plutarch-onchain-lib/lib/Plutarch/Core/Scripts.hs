module Plutarch.Core.Scripts(
  tryCompile,
  tryCompileTracingAndBinds,
  tryCompileNoTracing
  ) where

import           Plutarch        (ClosedTerm, Config (..), LogLevel (LogInfo),
                                  TracingMode (DoTracingAndBinds), compile)
import           Plutarch.Script (Script)

tryCompile :: Config -> ClosedTerm a -> Script
tryCompile cfg x = case compile cfg x of
  Left e  -> error $ "Compilation failed: " <> show e
  Right s -> s

tryCompileTracingAndBinds :: ClosedTerm a -> Script
tryCompileTracingAndBinds = tryCompile (Tracing LogInfo DoTracingAndBinds)

tryCompileNoTracing :: ClosedTerm a -> Script
tryCompileNoTracing = tryCompile NoTracing





