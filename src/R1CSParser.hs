{-# LANGUAGE OverloadedStrings #-}

module R1CSParser(parseR1CSIR, toLean) where

import Control.Monad (replicateM)
import qualified Data.ByteString as BS
import Data.List (intersperse)
import Data.Word
import Text.Megaparsec
import Text.Megaparsec.Byte
import Text.Megaparsec.Byte.Binary (word32le, word64le)

type Parser a = Parsec String BS.ByteString a

data R1CSFileSection =
                       SHeader Word32 Integer Word32 Word32 Word32 Word32 Word64 Word32
                     | SConstraints BS.ByteString
                     | SWire2LabelId BS.ByteString
                     | SUltraPLONKCustomGateList BS.ByteString
                     | SUltraPLONKCustomGateApplication BS.ByteString
    deriving Show

isHeader :: R1CSFileSection -> Bool
isHeader (SHeader _ _ _ _ _ _ _ _) = True
isHeader _ = False

isConstraints :: R1CSFileSection -> Bool
isConstraints (SConstraints _) = True
isConstraints _ = False

isWire2LabelId :: R1CSFileSection -> Bool
isWire2LabelId (SWire2LabelId _) = True
isWire2LabelId _ = False



data R1CSFile = R1CSFile { version :: Word32, numSections :: Word32, sections :: [R1CSFileSection]}
              deriving Show

data R1CSConfig =
    R1CSConfig
    {
      fieldElemSize :: Word32,
      prime :: Integer,
      nWires :: Word32,
      nPubOut :: Word32,
      nPubIn :: Word32,
      nPrvIn :: Word32,
      nLabels :: Word64,
      mConstraints :: Word32
    }
                deriving Show

data Constraints = Constraints [([(Word32, Integer)], [(Word32, Integer)], [(Word32, Integer)])]
                   deriving Show

data Wire2LabelId = Wire2LabelId [Word64]
                    deriving Show

parseLEInteger :: Int -> Parser Integer
parseLEInteger sz = do
  w8s <- replicateM sz (satisfy (const True))
  pure (foldr (\w8 i -> (toInteger w8) + 256 * i) 0 w8s)

r1csHeaderParser :: Parser (Word32, Integer, Word32, Word32, Word32, Word32, Word64, Word32)
r1csHeaderParser = do
  fieldElemSize <- word32le
  prime <- parseLEInteger (fromEnum fieldElemSize)
  nWires <- word32le
  nPubOut <- word32le
  nPubIn <- word32le
  nPrvIn <- word32le
  nLabels <- word64le
  mConstraints <- word32le
  pure (fieldElemSize, prime, nWires, nPubOut, nPubIn, nPrvIn, nLabels, mConstraints)

r1csSectionParser :: Parser R1CSFileSection
r1csSectionParser = do
  secType <- word32le
  secSize <- word64le
  case secType of
    1 -> do
      (fieldElemSize, prime, nWires, nPubOut, nPubIn, nPrvIn, nLabels, mConstraints) <- r1csHeaderParser
      pure (SHeader fieldElemSize prime nWires nPubOut nPubIn nPrvIn nLabels mConstraints)
    2 -> replicateM (fromEnum secSize) (satisfy (const True)) >>= pure . SConstraints . BS.pack
    3 -> replicateM (fromEnum secSize) (satisfy (const True)) >>= pure . SWire2LabelId . BS.pack
    4 -> replicateM (fromEnum secSize) (satisfy (const True)) >>= pure . SUltraPLONKCustomGateList . BS.pack
    5 -> replicateM (fromEnum secSize) (satisfy (const True)) >>= pure . SUltraPLONKCustomGateApplication . BS.pack
    n -> fail ("Unknown section type: " ++ (show n))


r1csFileParser :: Parser R1CSFile
r1csFileParser = do
  _ <- string "r1cs"
  version <- word32le
  numSections <- word32le
  sections <- replicateM (fromEnum numSections) r1csSectionParser
  eof
  pure (R1CSFile {version = version, numSections = numSections, sections = sections})

parseConstraintSection :: R1CSConfig -> BS.ByteString -> Either (ParseErrorBundle BS.ByteString String) Constraints
parseConstraintSection config bs =
    flip (flip runParser "") bs $ do
      constrs <- replicateM (fromEnum . mConstraints $ config) $ do
        nA <- word32le
        as <- replicateM (fromEnum nA) $ do
                wireId <- word32le
                a_coeff <- parseLEInteger (fromEnum . fieldElemSize $ config)
                pure (wireId, a_coeff)
        nB <- word32le
        bs <- replicateM (fromEnum nB) $ do
                wireId <- word32le
                b_coeff <- parseLEInteger (fromEnum . fieldElemSize $ config)
                pure (wireId, b_coeff)
        nC <- word32le
        cs <- replicateM (fromEnum nC) $ do
                wireId <- word32le
                c_coeff <- parseLEInteger (fromEnum . fieldElemSize $ config)
                pure (wireId, c_coeff)
        pure (as, bs, cs)
      pure (Constraints constrs)

parseWire2LabelIdSection :: R1CSConfig -> BS.ByteString -> Either (ParseErrorBundle BS.ByteString String) Wire2LabelId
parseWire2LabelIdSection config bs =
    flip (flip runParser "") bs $ replicateM (fromEnum $ nWires config) word64le >>= pure . Wire2LabelId

parseErr :: String -> Either (ParseErrorBundle BS.ByteString String) a
parseErr s = runParser (fail s) "" ""

parseR1CSIR :: BS.ByteString -> Either (ParseErrorBundle BS.ByteString String) (R1CSConfig, Constraints, Wire2LabelId)
parseR1CSIR file = do
  r1csFile <- runParser r1csFileParser "" $ file
  case filter isHeader (sections r1csFile) of
    [(SHeader fieldElemSize prime nWires nPubOut nPubIn nPrvIn nLabels mConstraints)] -> do
        let config = R1CSConfig fieldElemSize prime nWires nPubOut nPubIn nPrvIn nLabels mConstraints
        case (filter isConstraints (sections r1csFile), filter isWire2LabelId (sections r1csFile)) of
          ([SConstraints bs], [SWire2LabelId bs'])     -> do
                                             cons <- parseConstraintSection config bs
                                             lab  <- parseWire2LabelIdSection config bs'
                                             pure (config, cons, lab)
          _  -> parseErr "Wrong number of sections."
    e -> parseErr ("Headers: " ++ show e)

toConstraints :: ([(Word32, Integer)], [(Word32, Integer)], [(Word32, Integer)]) -> String
toConstraints (as, bs, cs) =
   "    (" ++ toSum as ++ ") * (" ++ toSum bs ++ ") = " ++ toSum cs
       where toSum [] = "0"
             toSum se = (concat . intersperse " + " . map (\(wID, coeff) -> (show coeff) ++ " * (w " ++ show wID ++ ")") $ se)

toLean :: String ->R1CSConfig -> Constraints -> String
toLean name config (Constraints constr) =
    "import Mathlib.Data.Nat.Prime.Defs\n" ++
    "import Mathlib.Data.ZMod.Basic\n\n" ++
    "namespace " ++ name ++ "\n\n" ++
    "def p : ℕ := " ++ show (prime config) ++ "\n" ++
    "axiom p_prime : p.Prime\n" ++
    "instance : Fact p.Prime := by rw [fact_iff]; exact p_prime\n\n" ++
    "def Witness : Type := Fin " ++ show (nLabels config) ++ " → ZMod p\n\n" ++
    "def spec (w : Witness) : Prop := sorry\n\n" ++
    "def circuit (w : Witness) : Prop := \n" ++
    (concat . intersperse (" ∧\n") . map toConstraints $ constr) ++ "\n\n" ++
    "example : ∀ w : Witness, w 0 = 1 → circuit w → spec w := by\n" ++
    "    unfold circuit spec\n" ++
    "    intros w w0_is_1\n" ++
    "    simp only [w0_is_1, one_mul, zero_add]\n" ++
    "    intros h\n" ++
    "    sorry\n\n" ++
    "end " ++ name
