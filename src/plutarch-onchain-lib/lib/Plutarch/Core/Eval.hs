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
  ptraces,
  toHexString,
  toBuiltinHexString,
  writeScriptBytesFile,
  encodeSerialiseCBOR,
  writePlutusScript,
  writePlutusScriptTraceBind,
  writePlutusScriptTrace,
  writePlutusScriptNoTrace,
  calcBudgetNoTraces,
  ) where

import Cardano.Binary qualified as CBOR
import Data.Aeson (KeyValue ((.=)), object)
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Bifunctor (first)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short (toShort)
import Data.Char (toLower)
import Data.Text (Text, pack, unpack)
import Data.Text qualified as T
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified
import Data.Word (Word8)
import Plutarch.Evaluate (applyArguments, evalScript, evalScriptHuge)
import Plutarch.Internal.Term (Config (..), LogLevel (..), S, Term,
                               TracingMode (..), compile)
import Plutarch.Pretty (prettyScript)
import Plutarch.Script (Script, deserialiseScript, serialiseScript)
import PlutusLedgerApi.V2 (BuiltinByteString, Data, ExBudget)
import PlutusTx.Prelude qualified as P
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.String (renderString)
import Test.Tasty.HUnit (HasCallStack)

encodeSerialiseCBOR :: Script -> Text
encodeSerialiseCBOR = Text.decodeUtf8 . Base16.encode . CBOR.serialize' . serialiseScript

type ClosedTerm a = (forall (s' :: S). Term s' a)

evalT :: Config -> ClosedTerm a -> Either Text (Script, ExBudget, [Text])
evalT cfg x = evalWithArgsT cfg x []

evalWithArgsT :: Config -> ClosedTerm a -> [Data] -> Either Text (Script, ExBudget, [Text])
evalWithArgsT cfg x args = do
  cmp <- compile cfg x
  let (escr, budg, trc) = evalScript $ applyArguments cmp args
  scr <- first (pack . show) escr
  pure (scr, budg, trc)

calcBudgetNoTraces :: ClosedTerm a -> [Data] -> ExBudget
calcBudgetNoTraces x args =
  let cmp = compile NoTracing x
  in  case cmp of
        Left e -> error $ "Failed to compile term: " <> show e
        Right scr ->
          let (_, budg, _) = evalScript $ applyArguments scr args
          in budg

writePlutusScript :: Config -> String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScript cfg title filepath term = do
  case evalT cfg term of
    Left e -> print e
    Right (script, _, _) -> do
      let
        scriptType = "PlutusScriptV2" :: String
        plutusJson = object ["type" .= scriptType, "description" .= title, "cborHex" .= encodeSerialiseCBOR script]
        content = encodePretty plutusJson
      LBS.writeFile filepath content

writePlutusScriptTraceBind :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTraceBind = writePlutusScript (Tracing LogInfo DoTracingAndBinds)

writePlutusScriptTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptTrace = writePlutusScript (Tracing LogInfo DoTracing)

writePlutusScriptNoTrace :: String -> FilePath -> ClosedTerm a -> IO ()
writePlutusScriptNoTrace = writePlutusScript NoTracing

comp :: ClosedTerm a -> Script
comp t = either (error . unpack) id $ compile (Tracing LogInfo DoTracing) t

-- | Asserts that the term evaluates successfully with the given trace sequence
ptraces :: ClosedTerm a -> [Text]
ptraces p =
  case evalScriptHuge $ comp p of
    (Left _, _, _) -> error "Term failed to evaluate"
    (Right _, _, traceLog) ->
      traceLog


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
