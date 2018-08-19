{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE BangPatterns #-}
-- {-# LANGUAGE DeriveGeneric #-}
-- {-# LANGUAGE DeriveAnyClass #-}

module FunctionalsZ2
     ( writeSDPtoFile
     , maxOPESDPFull113Z2
     )
 where

import GHC.Generics (Generic)
import Blocks
import SimplePoly
import Data.List
import Numeric.AD
import WriteXMLSDP
import Control.DeepSeq

data Prefactor a = ShortPrefactor { den :: a -> a }
                 | LongPrefactor { den :: a -> a }

shortPrefactor :: (Floating a) => RhoOrder -> Prefactor a
shortPrefactor n = ShortPrefactor { den = denominator00 n }

longPrefactor :: (Floating a) => RhoOrder -> Prefactor a
longPrefactor n = LongPrefactor { den = denominator n }

data Crossingeqnders a = Crossingeqnders { pref :: Prefactor a
                                         , polys :: [Poly a]
                                         , idty :: [a]
                                         , at :: a -> [a]
                                         }

newtype PolyVectorMatrix a = PolyVectorMatrix { els :: [[[Poly a]]] }

data FunctionalEls a = FunctionalEls { constraints :: [PolyVectorMatrix a]
                                     , norm :: [a]
                                     , obj :: [a]
                                     }

data SDP a = SDP { pvms :: [PolyVectorMatrix a], optvec :: [a] }

-------------------------------------------------------------------------------
-- Auxiliary functions for deriving crossing equations
-------------------------------------------------------------------------------
nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z : nestmap f z xs

productrule' :: (Algebra b a) => b -> a -> a
productrule' x y = x .* y

productrule :: Algebra b a => [b] -> [a] -> [a]
productrule ds es =
  crossdiagonalsums $ zipWith (zipWith (*)) diffstab binomialstab
  where
    diffstab = [ [ d .* e | d <- ds ] | e <- es ]

binomialstab :: Num a => [[a]]
binomialstab = binomialsrows $ map fromInteger [1,1..]
  where binomialsrows r = r : binomialsrows (nestmap (+) 0 r)

crossdiagonalsums :: Num a => [[a]] -> [a]
crossdiagonalsums (x:xs) =
  zipWith (+) (x ++ take (length xs) (map fromInteger [0,0..])) (0:crossdiagonalsums xs)
crossdiagonalsums [] = map fromInteger [0,0..]

onlyOdds :: [a] -> [a]
onlyOdds (x:y:xs) = y : onlyOdds xs
onlyOdds _ = []

onlyEvens :: [a] -> [a]
onlyEvens (x:y:xs) = x : onlyEvens xs
onlyEvens x = x

signAlternate :: (Num a) => [a] -> [a]
signAlternate (x:y:xs) = x:(-y):signAlternate xs
signAlternate x = x

withTypeOf :: a -> a -> a
withTypeOf x y = x

rescalefact :: (Floating a, Algebra a b) => a -> [b] -> [b]
rescalefact x = zipWith (.*) (scanl (/) x (fromInteger <$> [1..]))

diffslist :: (Floating a) => a -> [a]
diffslist htot = diffs (\x -> (1-x) ** auto htot) (1/2)

crossingeqndersSimpleEqn :: (Eq a, Floating a) => a -> RhoOrder -> a -> Crossingeqnders a
-- s is overall rescaling
crossingeqndersSimpleEqn h1 n s =
  Crossingeqnders
  { pref = shortPrefactor n
  , polys = parseP (numeratorpolys00 n)
  , idty = parseN (1 : repeat 0)
  -- , idty = onlyOdds . rescalefact s . productrule (diffslist (2 * h1)) $ (1 : repeat 0)
  , at = parseN . diffsblock00
  }
  where
    parseP = onlyOdds . rescalefact s . productrule (diffslist (2 * h1))
    parseN = onlyOdds . rescalefact s . productrule (diffslist (2 * h1))

crossingeqndersEqn1 :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn1 h1 _ n = crossingeqndersSimpleEqn h1 n 2

crossingeqndersEqn2 :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn2 _ h3 n = crossingeqndersSimpleEqn h3 n 2

crossingeqndersEqn6LHS :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn6LHS h1 h3 n =
  Crossingeqnders
  { pref = shortPrefactor n
  , polys = parseP (numeratorpolys00 n)
  , idty = parseN (1 : repeat 0)
  , at = parseN . diffsblock00
  }
  where
    parseP = rescalefact (1/2 `withTypeOf` h1) . productrule (diffslist (h1 + h3))
    parseN = rescalefact (1/2 `withTypeOf` h1) . productrule (diffslist (h1 + h3))

crossingeqndersEqn6RHS :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn6RHS h1 h3 n =
  Crossingeqnders
  { pref = longPrefactor n
  , polys = parseP (numeratorpolys (h3 - h1) (h3 - h1) n)
  , idty = undefined
  , at = parseN . diffsblock (h3 - h1) (h3 - h1)
  }
  where
    parseP = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule (diffslist (2 * h3))
    parseN = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule (diffslist (2 * h3))


crossingeqndersEqn5 :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn5 h1 h3 n =
  Crossingeqnders
  { pref = longPrefactor n
  , polys = parseP (numeratorpolys (h1 - h3) (h3 - h1) n)
  , idty = undefined
  , at = parseN . diffsblock (h1 - h3) (h3 - h1)
  }
  where
    parseP = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule (diffslist (h1 + h3))
    parseN = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule (diffslist (h1 + h3))

shiftpolys gap pvm = PolyVectorMatrix { els = (map . map . map) (shiftPoly gap) (els pvm) }
normalizepolys normvec pvm = PolyVectorMatrix { els = (map . map) (normalizewith normvec) (els pvm) }

combinecrossingeqnders :: (Eq a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> FunctionalEls a
combinecrossingeqnders n nd h1 h3 rat gapPpZp gapPpZm gapPmZm =
  FunctionalEls
  { constraints =
      [ shiftpolys gapPpZp
        PolyVectorMatrix {
          els = [[ polys1    , polys6LHS ]
                ,[ polys6LHS , polys2    ]]
        }
      , shiftpolys gapPpZm
        PolyVectorMatrix {
          els = [[ zipWith (+) polys6RHS polys5 ]]
        }
      , shiftpolys gapPmZm
        PolyVectorMatrix {
          els = [[ zipWith (-) polys6RHS polys5 ]]
        }
      ]
    , norm = zipWith5 (\x y z u v -> x + y + z + 2 * rat * u + rat * rat * v)
               norm6RHS norm5 norm1 norm6LHS norm2
    , obj = zipWith3 (\x y z -> x + 2 * y + z) identity1 identity6 identity2
  }
  where
    [nd1, nd2, nd5, nd6] = [nd, nd, nd, nd `quot` 2]
    tovec1 x = take nd1 x ++ replicate (nd2 + nd5 + nd6) 0
    tovec2 x = replicate nd1 0 ++ take nd2 x ++ replicate (nd5 + nd6) 0
    tovec5 x = replicate (nd1 + nd2) 0 ++ take nd5 x ++ replicate nd6 0
    tovec6 x = replicate (nd1 + nd2 + nd5) 0 ++ take nd6 x
    polys1 = tovec1 $ polys $ crossingeqndersEqn1 h1 h3 n
    polys2 = tovec2 $ polys $ crossingeqndersEqn2 h1 h3 n
    polys5 = tovec5 $ polys $ crossingeqndersEqn5 h1 h3 n
    polys6LHS = tovec6 $ polys $ crossingeqndersEqn6LHS h1 h3 n
    polys6RHS = tovec6 $ polys $ crossingeqndersEqn6RHS h1 h3 n
    identity1 = tovec1 $ idty $ crossingeqndersEqn1 h1 h3 n
    identity2 = tovec2 $ idty $ crossingeqndersEqn2 h1 h3 n
    identity6 = tovec6 $ idty $ crossingeqndersEqn6LHS h1 h3 n
    norm1 = tovec1 $ crossingeqndersEqn1 h1 h3 n `at` h3
    norm2 = tovec2 $ crossingeqndersEqn2 h1 h3 n `at` h3
    norm5 = tovec5 $ crossingeqndersEqn5 h1 h3 n `at` h1
    norm6LHS = tovec6 $ crossingeqndersEqn6LHS h1 h3 n `at` h3
    norm6RHS = tovec6 $ crossingeqndersEqn6RHS h1 h3 n `at` h1


-------------------------------------------------------------------------------
-- Auxiliary functions for deriving crossing equations
-------------------------------------------------------------------------------

dropEl :: Int -> [a] -> [a]
dropEl n xs = take n xs ++ drop (n+1) xs

normalizewith :: (Floating a, Ord a, Num b, Algebra a b) => [a] -> [b] -> [b]
normalizewith normvec polyvec =
  poly : dropEl maxloc (zipWith (\n p -> p - n .* poly) normvec polyvec)
  where
    (maxloc, maxval) = findExtr normvec
    poly = (1 / maxval) .* (polyvec !! maxloc)

findExtr :: (Num a, Ord a) => [a] -> (Int, a)
findExtr (x:xs) = findExtrRec xs x 0 1

findExtrRec :: (Num a, Ord a) => [a] -> a -> Int -> Int -> (Int, a)
findExtrRec [] prevMax prevPos curPos = (prevPos, prevMax)
findExtrRec (x:xs) prevMax prevPos curPos
  | abs x > abs prevMax = findExtrRec xs x curPos (curPos + 1)
  | otherwise           = findExtrRec xs prevMax prevPos (curPos + 1)

normalize :: (Floating a, Ord a) => FunctionalEls a -> SDP a
normalize fnels  = SDP { pvms = normalizepolys (norm fnels) <$> constraints fnels
                       , optvec = normalizewith (norm fnels) (obj fnels)
                       }

maxOPESDPFull113Z2 :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> SDP a
maxOPESDPFull113Z2 n nd h1 h3 gapPpZp gapPpZm gapPmZm rat =
  normalize $ combinecrossingeqnders n nd h1 h3 rat gapPpZp gapPpZm gapPmZm

writeSDPtoFile :: (Floating a, Show a) => FilePath -> SDP a -> IO ()
writeSDPtoFile fp sdp = writeXMLSDPtoFile fp (optvec sdp) (els <$> pvms sdp)
