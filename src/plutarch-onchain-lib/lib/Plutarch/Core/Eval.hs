{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plutarch.Core.Eval
Description : Evaluating plutarch terms
Copyright   : (c) Philip DiSarro, 2024
Stability   : experimental

-}
module Plutarch.Core.Eval(
  evalT,
  evalWithArgsT,
  psucceeds,
  passert,
  ptraces,
  toHexString,
  toBuiltinHexString,
  writeScriptBytesFile,
  encodeSerialiseCBOR,
  writePlutusScript,
  writePlutusScriptTraceBind,
  writePlutusScriptTrace,
  writePlutusScriptNoTrace,
  ) where

import qualified Cardano.Binary              as CBOR
import           Data.Aeson                  (KeyValue ((.=)), object)
import           Data.Aeson.Encode.Pretty    (encodePretty)
import           Data.Bifunctor              (first)
import qualified Data.ByteString             as BS
import qualified Data.ByteString.Base16      as Base16
import qualified Data.ByteString.Lazy        as LBS
import           Data.ByteString.Short       (toShort)
import           Data.Char                   (toLower)
import           Data.Text                   (Text, pack, unpack)
import qualified Data.Text                   as T
import qualified Data.Text.Encoding          as Text
import qualified Data.Text.IO
import           Data.Word                   (Word8)
import           Plutarch                    (Config (..), LogLevel (..),
                                              TracingMode (..), compile,
                                              prettyScript, printScript)
import           Plutarch.Evaluate           (applyArguments, evalScript,
                                              evalScriptHuge)
import           Plutarch.Prelude
import           Plutarch.Script             (Script, deserialiseScript,
                                              serialiseScript)
import           PlutusLedgerApi.V2          (BuiltinByteString, Data, ExBudget)
import qualified PlutusTx.Prelude            as P
import           Prettyprinter               (defaultLayoutOptions,
                                              layoutPretty)
import           Prettyprinter.Render.String (renderString)
import           Test.Tasty.HUnit            (Assertion, HasCallStack,
                                              assertEqual, assertFailure)

encodeSerialiseCBOR :: Script -> Text
encodeSerialiseCBOR = Text.decodeUtf8 . Base16.encode . CBOR.serialize' . serialiseScript

evalT :: Config -> ClosedTerm a -> Either Text (Script, ExBudget, [Text])
evalT cfg x = evalWithArgsT cfg x []

evalWithArgsT :: Config -> ClosedTerm a -> [Data] -> Either Text (Script, ExBudget, [Text])
evalWithArgsT cfg x args = do
  cmp <- compile cfg x
  let (escr, budg, trc) = evalScript $ applyArguments cmp args
  scr <- first (pack . show) escr
  pure (scr, budg, trc)

writePlutusScript :: Config -> String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScript cfg title filepath term = do
  case evalT cfg term of
    Left e -> putStrLn (show e)
    Right (script, _, _) -> do
      let
        scriptType = "PlutusScriptV2" :: String
        plutusJson = object ["type" .= scriptType, "description" .= title, "cborHex" .= encodeSerialiseCBOR script]
        content = encodePretty plutusJson
      LBS.writeFile filepath content

writePlutusScriptTraceBind :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTraceBind title filepath term =
  writePlutusScript (Tracing LogInfo DoTracingAndBinds) title filepath term

writePlutusScriptTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTrace title filepath term =
  writePlutusScript (Tracing LogInfo DoTracing) title filepath term

writePlutusScriptNoTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptNoTrace title filepath term =
  writePlutusScript NoTracing title filepath term

comp :: ClosedTerm a -> Script
comp t = either (error . unpack) id $ compile (Tracing LogInfo DoTracing) t

-- | Asserts the term evaluates successfully without failing
psucceeds :: ClosedTerm a -> Assertion
psucceeds p =
  case evalScriptHuge $ comp p of
    (Left _, _, trc) -> assertFailure ("Term failed to evaluate: " ++ show trc)
    (Right _, _, _)  -> pure ()

pscriptShouldBe :: Script -> Script -> Assertion
pscriptShouldBe x y =
  assertEqual "pscriptShouldBe" (printScript x) (printScript y)

pshouldBe :: ClosedTerm a -> ClosedTerm b -> Assertion
pshouldBe x y = do
  p1 <- eval $ comp x
  p2 <- eval $ comp y
  pscriptShouldBe p1 p2
  where
    eval s = case evalScriptHuge s of
      (Left e, _, _)   -> assertFailure $ "Script evaluation failed: " <> show e
      (Right x', _, _) -> pure x'

(#@?=) :: ClosedTerm a -> ClosedTerm b -> Assertion
(#@?=) = pshouldBe

-- | Asserts the term to be true
passert :: ClosedTerm a -> Assertion
passert p = p #@?= pconstant True

-- | Asserts that the term evaluates successfully with the given trace sequence
ptraces :: ClosedTerm a -> [Text] -> Assertion
ptraces p develTraces =
  case evalScript $ comp p of
    (Left _, _, _) -> assertFailure "Term failed to evaluate"
    (Right _, _, traceLog) ->
      assertEqual "ptraces: does not match expected" traceLog develTraces


toBuiltinHexString :: String -> BuiltinByteString
toBuiltinHexString = P.toBuiltin . toHexString

toHexString :: String -> BS.ByteString
toHexString =
  BS.pack . f
  where
    f ""             = []
    f [_]            = error "UnevenLength"
    f (x : y : rest) = (hexDigitToWord8 x * 16 + hexDigitToWord8 y) : f rest

hexDigitToWord8 :: HasCallStack => Char -> Word8
hexDigitToWord8 = f . toLower
  where
    f :: Char -> Word8
    f '0' = 0
    f '1' = 1
    f '2' = 2
    f '3' = 3
    f '4' = 4
    f '5' = 5
    f '6' = 6
    f '7' = 7
    f '8' = 8
    f '9' = 9
    f 'a' = 10
    f 'b' = 11
    f 'c' = 12
    f 'd' = 13
    f 'e' = 14
    f 'f' = 15
    f c   = error ("InvalidHexDigit " <> [c])

writeScriptBytesFile :: FilePath -> BS.ByteString -> IO ()
writeScriptBytesFile path script = do
  let scriptBytes = deserialiseScript (toShort script)
      renderedScript = renderString $ layoutPretty defaultLayoutOptions (prettyScript scriptBytes)
  Data.Text.IO.writeFile path (T.pack renderedScript)
