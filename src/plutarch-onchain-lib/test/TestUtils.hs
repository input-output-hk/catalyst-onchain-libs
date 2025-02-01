module TestUtils (testEval) where
import Data.Text qualified as Text
import Plutarch.Internal.Term
import Plutarch.Prelude
import Plutarch.Test.Unit (TermResult (..), evalTermResult)
import Test.Tasty
import Test.Tasty.HUnit

{- | Assert that term compiled and evaluated without errors

-}
testEval :: TestName -> ClosedTerm a -> TestTree
testEval name term = testCase name $ do
  case evalTermResult (Tracing LogDebug DoTracingAndBinds) term of
    FailedToCompile err -> assertFailure $ "Failed to compile: " <> Text.unpack err
    FailedToEvaluate err traces -> assertFailure $ "Failed to evaluate: " <> show err <> "\n" <> show traces
    Evaluated _ _ -> pure ()
