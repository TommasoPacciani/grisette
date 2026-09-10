{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.SymPrim.IntegerSerializationTests (integerSerializationTests) where

import Control.Monad (replicateM)
import qualified Data.Binary as Binary
import qualified Data.Binary.Get as BinaryGet
import qualified Data.Binary.Put as BinaryPut
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Lazy as LazyByteString
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Ratio ((%))
import qualified Data.Serialize as Cereal
import qualified Data.Serialize.Get as CerealGet
import qualified Data.Serialize.Put as CerealPut
import Data.Word (Word8)
import Grisette
  ( AlgReal (..),
    AlgRealPoly (AlgRealPoly),
    Identifier,
    Model,
    ModelOps (emptyModel, insertValue),
    RealPoint (ClosedPoint, OpenPoint),
    SExpr (Atom, List, NumberAtom),
    SymInteger,
    TypedAnySymbol,
    TypedConstantSymbol,
    withMetadata,
    (-->),
    type (-->),
    type (=->) (TabularFun),
  )
import qualified Grisette.Internal.SymPrim.Array as Array
import Grisette.Internal.SymPrim.Nominal
  ( Nominal (Nominal),
    NominalDomain (Domain),
  )
import Grisette.Internal.SymPrim.Prim.Term
  ( ModelValue,
    Term,
    conTerm,
    ssymTerm,
    toModelValue,
  )
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertEqual, assertFailure)

integerSerializationTests :: Test
integerSerializationTests =
  testGroup
    "signed Integer serialization"
    [ testGroup "Serial wire goldens and framing"
        [ testCase label $ assertSerialWire [value] octets
        | (label, value, octets) <- wireGoldens
        ],
      testCase "concatenated signed values retain every boundary" $
        assertSerialWire
          [value | (_, value, _) <- wireGoldens]
          (concat [octets | (_, _, octets) <- wireGoldens]),
      testGroup "legacy positive decoding remains permissive"
        [ testCase label $ assertSerialReads [value] octets
        | (label, value, octets) <-
            [ ("overlong one", 1, [0x81, 0x00]),
              ("overlong 127", 127, [0xff, 0x00]),
              ("overlong 128", 128, [0x80, 0x81, 0x00]),
              ("overlong zero outside the signed escape", 0, [0x80, 0x80, 0x00])
            ]
        ],
      testGroup "malformed signed encodings are rejected"
        [ testCase label $ assertRejected octets
        | (label, octets) <-
            [ ("incomplete positive continuation", [0x80]),
              ("signed escape without magnitude", [0x80, 0x00]),
              ("incomplete negative magnitude", [0x80, 0x00, 0x80]),
              ("negative zero", [0x80, 0x00, 0x00]),
              ("noncanonical negative one", [0x80, 0x00, 0x81, 0x00]),
              ("noncanonical negative zero", [0x80, 0x00, 0x80, 0x00])
            ]
        ],
      testGroup "nested consumers"
        [ testCase "negative scalar ConTerm" $
            assertRoundTrip (conTerm (-17 :: Integer)),
          testCase "ConTerm recursively carries pair, sequence and nominal values" $
            assertRoundTrip
              ( conTerm (-1, [Nominal (-128), Nominal (-129)]) ::
                  Term
                    ( Integer,
                      [Nominal ('Domain "signed-serialization" '[]) Integer]
                    )
              ),
          testCase "array default, key and value are all signed" $ do
            let value = Array.store (Array.const (-11)) (-22) (-33)
                  :: Array.Array Integer Integer
            assertRoundTrip value
            assertRoundTrip (conTerm value),
          testCase "exact rational and its ConTerm retain a negative numerator" $ do
            let value = AlgExactRational ((-7) % 3)
            assertRoundTrip value
            assertRoundTrip (conTerm value),
          testCase "inexact rational retains a negative numerator" $ do
            let value = AlgInexactRational ((-5) % 2)
            assertConsumerRoundTrip value (assertAlgReal value),
          testCase "polynomial root retains its negative coefficient" $ do
            let value = AlgPolyRoot 1 (AlgRealPoly [(1, 2), (-2, 0)]) Nothing
            assertConsumerRoundTrip value (assertAlgReal value),
          testCase "interval retains negative open and closed bounds" $ do
            let value = AlgInterval
                  (OpenPoint ((-3) % 2)) (ClosedPoint ((-1) % 2))
            assertConsumerRoundTrip value (assertAlgReal value),
          testCase "ModelValue retains signed nested data and its type" $
            assertRoundTrip
              (toModelValue ((-2, [-3]) :: (Integer, [Integer])) :: ModelValue),
          testCase "Model retains signed scalar and nested assignments" $ do
            let value = insertValue
                  ("signed.scalar" :: TypedAnySymbol Integer) (-1)
                  (insertValue
                    ("signed.nested" :: TypedAnySymbol (Integer, [Integer]))
                    (-2, [-3]) emptyModel) :: Model
            assertRoundTrip value,
          testCase "SExpr retains a negative NumberAtom before another child" $
            assertRoundTrip (List [NumberAtom (-1), Atom "tail"]),
          testCase "Identifier and typed symbol retain signed metadata" $ do
            let value = withMetadata "signed.identifier" (NumberAtom (-129))
                  :: Identifier
            assertRoundTrip value
            assertRoundTrip (ssymTerm value :: Term Integer),
          testCase "GeneralFun and its ConTerm retain a negative body constant" $ do
            let value =
                  ("signed.argument" :: TypedConstantSymbol Integer)
                    --> ("signed.argument" - 17 :: SymInteger)
                  :: Integer --> Integer
            assertRoundTrip value
            assertRoundTrip (conTerm value),
          testCase "TabularFun and its ConTerm retain negative keys, values and default" $ do
            let value = TabularFun [(-1, -2)] (-3) :: Integer =-> Integer
            assertRoundTrip value
            assertRoundTrip (conTerm value)
        ]
    ]

-- These bytes are fixed format witnesses, not output from another varint
-- encoder. In the large case, 4096 = 7 * 585 + 1: the low digit is 17,
-- followed by 584 zero continuation digits and the final digit 2.
wireGoldens :: [(String, Integer, [Word8])]
wireGoldens =
  [ ("zero", 0, [0x00]),
    ("127", 127, [0x7f]),
    ("128", 128, [0x80, 0x01]),
    ("255", 255, [0xff, 0x01]),
    ("256", 256, [0x80, 0x02]),
    ("16383", 16383, [0xff, 0x7f]),
    ("16384", 16384, [0x80, 0x80, 0x01]),
    ("negative one", -1, [0x80, 0x00, 0x01]),
    ("negative two", -2, [0x80, 0x00, 0x02]),
    ("negative 128", -128, [0x80, 0x00, 0x80, 0x01]),
    ("negative 129", -129, [0x80, 0x00, 0x81, 0x01]),
    ("negative 255", -255, [0x80, 0x00, 0xff, 0x01]),
    ("negative 256", -256, [0x80, 0x00, 0x80, 0x02]),
    ("2^4096 + 17", hugeMagnitude, hugeWire),
    ("negative (2^4096 + 17)", negate hugeMagnitude, 0x80 : 0x00 : hugeWire)
  ]
  where
    hugeMagnitude = 2 ^ (4096 :: Int) + 17
    hugeWire = 0x91 : replicate 584 0x80 ++ [0x02]

-- Calling Binary.encode or Cereal.encode on a raw Integer would test those
-- packages' own Integer instances, not the Serial Integer owner used by terms.
assertSerialWire :: [Integer] -> [Word8] -> Assertion
assertSerialWire values octets = do
  assertEqual "Binary Serial wire"
    (LazyByteString.pack octets)
    (BinaryPut.runPut (mapM_ serialize values))
  assertEqual "Cereal Serial wire"
    (ByteString.pack octets)
    (CerealPut.runPut (mapM_ serialize values))
  assertSerialReads values octets

assertSerialReads :: [Integer] -> [Word8] -> Assertion
assertSerialReads values octets = do
  let framed = octets ++ [0x5a, 0xa5]
      binaryReader = (,)
        <$> replicateM (length values) (deserialize :: BinaryGet.Get Integer)
        <*> BinaryGet.getWord8
      cerealReader = (,)
        <$> replicateM (length values) (deserialize :: CerealGet.Get Integer)
        <*> CerealGet.getWord8
  case BinaryGet.runGetOrFail binaryReader (LazyByteString.pack framed) of
    Left (_, _, message) -> assertFailure $ "Binary Serial decode: " ++ message
    Right (remaining, consumed, actual) -> do
      assertEqual "Binary signed values and sentinel" (values, 0x5a) actual
      assertEqual "Binary exact leftover" (LazyByteString.pack [0xa5]) remaining
      assertEqual "Binary exact consumed length" (fromIntegral (length octets + 1)) consumed
  case CerealGet.runGetState cerealReader (ByteString.pack framed) 0 of
    Left message -> assertFailure $ "Cereal Serial decode: " ++ message
    Right (actual, remaining) -> do
      assertEqual "Cereal signed values and sentinel" (values, 0x5a) actual
      assertEqual "Cereal exact leftover" (ByteString.pack [0xa5]) remaining

assertRejected :: [Word8] -> Assertion
assertRejected octets = do
  -- Do not append framing bytes here: a sentinel could complete a truncated
  -- magnitude and turn the intended malformed input into a valid number.
  case BinaryGet.runGetOrFail
      (deserialize :: BinaryGet.Get Integer) (LazyByteString.pack octets) of
    Left _ -> pure ()
    Right (_, _, value) -> assertFailure $
      "Binary accepted a malformed signed Integer: " ++ show value
  case CerealGet.runGetState
      (deserialize :: CerealGet.Get Integer) (ByteString.pack octets) 0 of
    Left _ -> pure ()
    Right (value, _) -> assertFailure $
      "Cereal accepted a malformed signed Integer: " ++ show value

assertRoundTrip ::
  (Binary.Binary value, Cereal.Serialize value, Eq value, Show value) =>
  value -> Assertion
assertRoundTrip expected =
  assertConsumerRoundTrip expected (assertEqual "decoded consumer value" expected)

-- Exercise the consumers' actual Binary/Cereal instances, including their
-- delegation to Serial. Check framing as well as the reconstructed value.
assertConsumerRoundTrip ::
  forall value.
  (Binary.Binary value, Cereal.Serialize value) =>
  value -> (value -> Assertion) -> Assertion
assertConsumerRoundTrip value check = do
  let binaryBytes = Binary.encode value <> LazyByteString.pack [0x5a, 0xa5]
      cerealBytes = Cereal.encode value <> ByteString.pack [0x5a, 0xa5]
      binaryReader = (,)
        <$> (Binary.get :: BinaryGet.Get value) <*> BinaryGet.getWord8
      cerealReader = (,)
        <$> (Cereal.get :: CerealGet.Get value) <*> CerealGet.getWord8
  case BinaryGet.runGetOrFail binaryReader binaryBytes of
    Left (_, _, message) -> assertFailure $ "Binary consumer decode: " ++ message
    Right (remaining, consumed, (actual, sentinel)) -> do
      assertEqual "Binary consumer sentinel" 0x5a sentinel
      assertEqual "Binary consumer exact leftover" (LazyByteString.pack [0xa5]) remaining
      assertEqual "Binary consumer exact consumed length" (LazyByteString.length binaryBytes - 1) consumed
      check actual
  case CerealGet.runGetState cerealReader cerealBytes 0 of
    Left message -> assertFailure $ "Cereal consumer decode: " ++ message
    Right ((actual, sentinel), remaining) -> do
      assertEqual "Cereal consumer sentinel" 0x5a sentinel
      assertEqual "Cereal consumer exact leftover" (ByteString.pack [0xa5]) remaining
      check actual

-- AlgReal's Eq intentionally throws outside exact rationals. Serialization
-- must preserve the representation of every constructor without invoking it.
assertAlgReal :: AlgReal -> AlgReal -> Assertion
assertAlgReal expected actual = case (expected, actual) of
  (AlgExactRational left, AlgExactRational right) ->
    assertEqual "exact rational" left right
  (AlgInexactRational left, AlgInexactRational right) ->
    assertEqual "inexact rational" left right
  (AlgPolyRoot leftIndex (AlgRealPoly leftPoly) leftApproximation,
      AlgPolyRoot rightIndex (AlgRealPoly rightPoly) rightApproximation) ->
    assertEqual "polynomial root fields"
      (leftIndex, leftPoly, leftApproximation)
      (rightIndex, rightPoly, rightApproximation)
  (AlgInterval leftLower leftUpper, AlgInterval rightLower rightUpper) ->
    assertBool "interval endpoints changed"
      (leftLower == rightLower && leftUpper == rightUpper)
  _ -> assertFailure $
    "algebraic real constructor changed: " ++ show expected ++ " -> " ++ show actual
