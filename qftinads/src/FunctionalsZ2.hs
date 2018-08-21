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

crossingeqndersSimpleEqn :: (Eq a, Floating a) => a -> [Poly a] -> a -> Crossingeqnders a
-- s is overall rescaling
crossingeqndersSimpleEqn h1 nums s =
  Crossingeqnders
  { pref = undefined -- shortPrefactor n
  , polys = onlyOdds . rescalefact s . productrule dl $ nums
  , idty = onlyOdds . rescalefact s . productrule dl $ (1 : repeat 0)
  , at = onlyOdds . rescalefact s . productrule dl . diffsblock00
  }
  where
    dl = diffslist (2 * h1)

crossingeqndersEqn1 :: (Eq a, Floating a) => a -> a -> [Poly a] -> Crossingeqnders a
crossingeqndersEqn1 h1 _ nums = crossingeqndersSimpleEqn h1 nums 2

crossingeqndersEqn2 :: (Eq a, Floating a) => a -> a -> [Poly a] -> Crossingeqnders a
crossingeqndersEqn2 _ h3 nums = crossingeqndersSimpleEqn h3 nums 2

crossingeqndersEqn6LHS :: (Eq a, Floating a) => a -> a -> [Poly a] -> Crossingeqnders a
crossingeqndersEqn6LHS h1 h3 nums =
  Crossingeqnders
  { pref = undefined -- shortPrefactor n
  , polys = rescalefact (1/2 `withTypeOf` h1) . productrule dl $ nums
  , idty = rescalefact (1/2 `withTypeOf` h1) . productrule dl $ (1 : repeat 0)
  , at = rescalefact (1/2 `withTypeOf` h1) . productrule dl . diffsblock00
  }
  where
    dl = diffslist (h1 + h3)

crossingeqndersEqn6RHS :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn6RHS h1 h3 n =
  Crossingeqnders
  { pref = undefined -- longPrefactor n
  , polys = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule dl $ numeratorpolys (h3 - h1) (h3 - h1) n
  , idty = undefined
  , at = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule dl . diffsblock (h3 - h1) (h3 - h1)
  }
  where
    dl = diffslist (2 * h3)

crossingeqndersEqn5 :: (Eq a, Floating a) => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn5 h1 h3 n =
  Crossingeqnders
  { pref = undefined -- longPrefactor n
  , polys = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl $ numeratorpolys (h1 - h3) (h3 - h1) n
  , idty = undefined
  , at = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl . diffsblock (h1 - h3) (h3 - h1)
  }
  where
    dl = diffslist (h1 + h3)

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
    polys1 = tovec1 $ polys ceqndsEqn1
    polys2 = tovec2 $ polys ceqndsEqn2
    polys5 = tovec5 $ polys ceqndsEqn5
    polys6LHS = tovec6 $ polys ceqndsEqn6LHS
    polys6RHS = tovec6 $ polys ceqndsEqn6RHS
    identity1 = tovec1 $ idty ceqndsEqn1
    identity2 = tovec2 $ idty ceqndsEqn2
    identity6 = tovec6 $ idty ceqndsEqn6LHS
    norm1 = tovec1 $ ceqndsEqn1 `at` h3
    norm2 = tovec2 $ ceqndsEqn2 `at` h3
    norm5 = tovec5 $ ceqndsEqn5 `at` h1
    norm6LHS = tovec6 $ ceqndsEqn6LHS `at` h3
    norm6RHS = tovec6 $ ceqndsEqn6RHS `at` h1
    nums00 = numeratorpolys00 n
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 nums00
    ceqndsEqn2 = crossingeqndersEqn2 h1 h3 nums00
    ceqndsEqn5 = crossingeqndersEqn5 h1 h3 n
    ceqndsEqn6LHS = crossingeqndersEqn6LHS h1 h3 nums00
    ceqndsEqn6RHS = crossingeqndersEqn6RHS h1 h3 n

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
