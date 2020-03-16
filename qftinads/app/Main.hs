{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where


import SimplePoly
import Blocks
import FunctionalsZ2
import Numeric.Rounded
import Text.XML.Light
import System.Environment
import Control.DeepSeq

-- Needed newtype instead of type to create instance NFData
newtype PFloat = PFloat (Rounded TowardZero 1024)
                 deriving (Eq, Ord, Num, Fractional, Floating)
-- Ugh, using newtype means standard derived Read and Show add "PFloat"
instance Read PFloat where
  readsPrec x s = [(PFloat y, s') | (y, s') <- readsPrec x s]
instance Show PFloat where
  show (PFloat x) = show x
instance NFData PFloat where
  rnf = (`seq` ()) -- whnf suffices

buildSdpFile :: Element -> IO ()
buildSdpFile xml =
  case getLeaf "function" of
    -- Just "feasibilitySDPSimple" ->
    --   let
    --     Just filename = getLeaf "filename"
    --     Just h1in = read <$> getLeaf "h1" :: Maybe PFloat
    --     Just gap = read <$> getLeaf "gap" :: Maybe PFloat
    --     Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
    --     Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
    --   in writeSDPtoFile filename $ feasibilitySDPSimple rhoOrder derOrder h1in gap
    -- Just "maxOPESDPSimple" ->
    --   let
    --     Just filename = getLeaf "filename"
    --     Just h1in = read <$> getLeaf "h1" :: Maybe PFloat
    --     Just gap = read <$> getLeaf "gap" :: Maybe PFloat
    --     Just hint = read <$> getLeaf "hint" :: Maybe PFloat
    --     Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
    --     Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
    --   in writeSDPtoFile filename $ maxOPESDPSimple rhoOrder derOrder h1in gap hint
    -- Just "maxOPESDPFull113Even" ->
    --   let
    --     Just filename = getLeaf "filename"
    --     Just h1in = read <$> getLeaf "h1" :: Maybe PFloat
    --     Just h3in = read <$> getLeaf "h3" :: Maybe PFloat
    --     Just ratin = read <$> getLeaf "rat" :: Maybe PFloat
    --     Just evengapin = read <$> getLeaf "evengap" :: Maybe PFloat
    --     Just oddgapin = read <$> getLeaf "oddgap" :: Maybe PFloat
    --     Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
    --     Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
    --   in writeSDPtoFile filename $ maxOPESDPFull113Even rhoOrder derOrder h1in h3in evengapin oddgapin ratin
    Just "feasibilitySDPSingle" ->
      let
        Just filename = getLeaf "filename"
        Just h1 = read <$> getLeaf "h1" :: Maybe PFloat
        Just h3 = read <$> getLeaf "h3" :: Maybe PFloat
        Just gap = read <$> getLeaf "gap" :: Maybe PFloat
        Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
        Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
        in writeSDPtoFile filename $ feasibilitySDPSingle rhoOrder derOrder h1 h3 gap
    Just "maxOPESDPSingle" ->
      let
        Just filename = getLeaf "filename"
        Just h1 = read <$> getLeaf "h1" :: Maybe PFloat
        Just h3 = read <$> getLeaf "h3" :: Maybe PFloat
        Just gap = read <$> getLeaf "gap" :: Maybe PFloat
        Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
        Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
        in writeSDPtoFile filename $ maxOPESDPSingle rhoOrder derOrder h1 h3 gap
    Just "maxOPESDPFull113Z2" ->
      let
        Just filename = getLeaf "filename"
        Just h1 = read <$> getLeaf "h1" :: Maybe PFloat
        Just h3 = read <$> getLeaf "h3" :: Maybe PFloat
        Just rat = read <$> getLeaf "rat" :: Maybe PFloat
        Just gapPevenZeven = read <$> getLeaf "pevenzevengap" :: Maybe PFloat
        Just gapPevenZodd = read <$> getLeaf "pevenzoddgap" :: Maybe PFloat
        Just gapPoddZodd = read <$> getLeaf "poddzoddgap" :: Maybe PFloat
        Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
        Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
        in writeSDPtoFile filename $ maxOPESDPFull113Z2 rhoOrder derOrder h1 h3 gapPevenZeven gapPevenZodd gapPoddZodd rat
    Just "feasibilitySDPFull113Z2" ->
      let
        Just filename = getLeaf "filename"
        Just h1 = read <$> getLeaf "h1" :: Maybe PFloat
        Just h3 = read <$> getLeaf "h3" :: Maybe PFloat
        Just rat = read <$> getLeaf "rat" :: Maybe PFloat
        Just gapPevenZeven = read <$> getLeaf "pevenzevengap" :: Maybe PFloat
        Just gapPevenZodd = read <$> getLeaf "pevenzoddgap" :: Maybe PFloat
        Just gapPoddZodd = read <$> getLeaf "poddzoddgap" :: Maybe PFloat
        Just rhoOrder = read <$> getLeaf "rhoOrder" :: Maybe Integer
        Just derOrder = read <$> getLeaf "derOrder" :: Maybe Int
        in writeSDPtoFile filename $ feasibilitySDPFull113Z2 rhoOrder derOrder h1 h3 gapPevenZeven gapPevenZodd gapPoddZodd rat
    Just _                      -> putStrLn "Error: Function not recognized"
    Nothing                     -> putStrLn "Error: No function specified"
  where
    -- getText :: Element -> String
    getText = cdData . head . onlyText . elContent
    -- getLeaf :: String -> Maybe String
    getLeaf s = getText <$> findChild (toQName s) xml

toQName :: String -> QName
toQName s = QName { qName = s, qURI = Nothing, qPrefix = Nothing }

showarr :: (Show a) => [a] -> IO ()
showarr xs = putStr $ unlines $ show <$> xs

main :: IO [()]
main = do
  file <- head <$> getArgs
  allXmlData <- onlyElems . parseXML <$> readFile file
  let allSdpFiles = concatMap (findChildren $ toQName "sdpFileData") allXmlData
  sequence $ buildSdpFile <$> allSdpFiles

-- main :: IO ()
-- main = showarr (take 150 $ numeratorpolys00 50 :: [Poly PFloat])
