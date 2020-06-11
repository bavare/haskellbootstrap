{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE BangPatterns #-}
-- {-# LANGUAGE DeriveGeneric #-}
-- {-# LANGUAGE DeriveAnyClass #-}

module FunctionalsZ2
     ( writeSDPtoFile
     , maxOPESDPFull113Z2
     , maxOPESDPSingle
     , feasibilitySDPSingle
     , feasibilitySDPFull113Z2
     , feasibilitySDPFull113Z2fixedOPE
     )
 where

import GHC.Generics (Generic)
import Blocks
import SimplePoly
import Data.List
import Numeric.AD
import WriteXMLSDP
import Control.DeepSeq
import PolyVectorMatrix

-- data Prefactor a = ShortPrefactor { coeff :: a
--                                   , poles :: [a]
--                                   , exponent :: a
--                                   , den :: a -> a  -- legacy - to be removed
--                                   }
--                  | LongPrefactor { coeff :: a
--                                  , poles :: [a]
--                                  , exponent :: a
--                                  , den :: a -> a -- legacy - to be removed
--                                  }

-- den' :: Prefactor a -> a -> a
-- den' p h = coeff p *

-- shortPrefactor :: (Floating a) => RhoOrder -> Prefactor a
-- shortPrefactor n = ShortPrefactor { den = denominator00 n }
--
-- longPrefactor :: (Floating a) => RhoOrder -> Prefactor a
-- longPrefactor n = LongPrefactor { den = denominator n }

data Blockders a = Blockders { bdpref :: DampedRational a
                             , bdnums :: [Poly a]
                             , bdidty :: [a]
                             }

data Crossingeqnders a = Crossingeqnders { pref :: DampedRational a
                                         , polys :: [Poly a]
                                         , idty :: [a]
                                         }

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

-- crossdiagonalsums :: Num a => [[a]] -> [a]
-- crossdiagonalsums (x:xs) =
--   zipWith (+) (x ++ take (length xs) (map fromInteger [0,0..])) (0:crossdiagonalsums xs)
-- crossdiagonalsums [] = map fromInteger [0,0..]

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

blockders :: Floating a => a -> a -> RhoOrder -> Blockders a
blockders a b n = Blockders { bdpref = dampedRational n
                            , bdnums = numeratorpolys a b n
                            , bdidty = undefined
                            }

blockders00 :: Floating a => RhoOrder -> Blockders a
blockders00 n = Blockders { bdpref = dampedRational00 n
                          , bdnums = numeratorpolys00 n
                          , bdidty = 1 : repeat 0
                          }

at :: Floating a => Crossingeqnders a -> a -> [a]
at ceqnders h = (\p -> dr * eval h p) <$> polys ceqnders
  where
    dr = evaldr (pref ceqnders) h

crossingeqndersEqn1 :: Floating a => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn1 h1 _ n =
  Crossingeqnders
  { pref = bdpref bds
  , polys = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl $ bdnums bds
  , idty = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl $ bdidty bds
  }
  where
    bds = blockders00 n
    dl = diffslist (2 * h1)

crossingeqndersEqn2 :: Floating a => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn2 _ h3 n =
  Crossingeqnders
  { pref = bdpref bds
  , polys = onlyOdds . rescalefact (2 `withTypeOf` h3) . productrule dl $ bdnums bds
  , idty = onlyOdds . rescalefact (2 `withTypeOf` h3) . productrule dl $ bdidty bds
  }
  where
    bds = blockders00 n
    dl = diffslist (2 * h3)

crossingeqndersEqn6LHS :: Floating a => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn6LHS h1 h3 n =
  Crossingeqnders
  { pref = bdpref bds
  , polys = rescalefact (1/2 `withTypeOf` h1) . productrule dl $ bdnums bds
  , idty = rescalefact (1/2 `withTypeOf` h1) . productrule dl $ bdidty bds
  }
  where
    bds = blockders00 n
    dl = diffslist (h1 + h3)

crossingeqndersEqn6RHS :: Floating a => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn6RHS h1 h3 n =
  Crossingeqnders
  { pref = bdpref bds
  , polys = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule dl $ bdnums bds
  , idty = undefined
  -- , at = signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule dl . diffsblock (h3 - h1) (h3 - h1)
  -- , evalApprox = \h n -> signAlternate . rescalefact (-1 `withTypeOf` h1) . productrule dl $ diffsblockapprox (h3 - h1) (h3 - h1) h n
  }
  where
    bds = blockders (h3 - h1) (h3 - h1) n
    dl = diffslist (2 * h3)

crossingeqndersEqn5 :: Floating a => a -> a -> RhoOrder -> Crossingeqnders a
crossingeqndersEqn5 h1 h3 n =
  Crossingeqnders
  { pref = bdpref bds
  , polys = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl $ bdnums bds
  , idty = undefined
  -- , at = onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl . diffsblock (h1 - h3) (h3 - h1)
  -- , evalApprox = \h n -> onlyOdds . rescalefact (2 `withTypeOf` h1) . productrule dl $ diffsblockapprox (h1 - h3) (h3 - h1) h n
  }
  where
    bds = blockders (h1 - h3) (h3 - h1) n
    dl = diffslist (h1 + h3)

shift gap pvm = PolyVectorMatrix { pvmpref = shiftdr gap (pvmpref pvm)
                                 , pvmpolys = (map . map . map) (shiftPoly gap) (pvmpolys pvm)
                                 }
normalizepolys normvec pvm = pvm { pvmpolys = (map . map) (normalizewith normvec) (pvmpolys pvm) }

combinecrossingeqnders :: Floating a => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> FunctionalEls a
combinecrossingeqnders n nd h1 h3 rat gapPpZp gapPpZm gapPmZm =
  FunctionalEls
  { constraints =
      [ shift gapPpZp
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn1
        , pvmpolys = [[ polys1    , polys6LHS ]
                     ,[ polys6LHS , polys2    ]]
        }
      , shift gapPpZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (+) polys6RHS polys5 ]]
        }
      , shift gapPmZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (-) polys6RHS polys5 ]]
        }
      ]
    , norm = zipWith5 (\x y z u v -> x + y + z + 2 * rat * u + rat * rat * v)
               norm6RHS norm5 norm1 norm6LHS norm2
    , obj = zipWith3 (\x y z -> x + 2 * y + z) identity1 identity6 identity2
  }
  where
    [nd1, nd2, nd5, nd6] = [nd, nd, nd, 2 * nd]
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
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 n
    ceqndsEqn2 = crossingeqndersEqn2 h1 h3 n
    ceqndsEqn5 = crossingeqndersEqn5 h1 h3 n
    ceqndsEqn6LHS = crossingeqndersEqn6LHS h1 h3 n
    ceqndsEqn6RHS = crossingeqndersEqn6RHS h1 h3 n


combinecrossingeqnders0opt :: Floating a => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> FunctionalEls a
combinecrossingeqnders0opt n nd h1 h3 rat gapPpZp gapPpZm gapPmZm =
  FunctionalEls
  { constraints =
      [ shift gapPpZp
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn1
        , pvmpolys = [[ polys1    , polys6LHS ]
                     ,[ polys6LHS , polys2    ]]
        }
      , shift gapPpZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (+) polys6RHS polys5 ]]
        }
      , shift gapPmZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (-) polys6RHS polys5 ]]
        }
      , PolyVectorMatrix {
          -- simple prefactor, used only to get non-trivial bilinearBasis
          pvmpref = dampedRational00 2
        , pvmpolys = [[ constP <$> zipWith3 (\x y z -> x + 2 * y + z) identity1 identity6 identity2 ]]
        }
      ]
    , norm = zipWith5 (\x y z u v -> x + y + z + 2 * rat * u + rat * rat * v)
               norm6RHS norm5 norm1 norm6LHS norm2
    , obj = replicate (nd1 + nd2 + nd5 + nd6) 0
  }
  where
    [nd1, nd2, nd5, nd6] = [nd, nd, nd, 2 * nd]
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
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 n
    ceqndsEqn2 = crossingeqndersEqn2 h1 h3 n
    ceqndsEqn5 = crossingeqndersEqn5 h1 h3 n
    ceqndsEqn6LHS = crossingeqndersEqn6LHS h1 h3 n
    ceqndsEqn6RHS = crossingeqndersEqn6RHS h1 h3 n


combinecrossingeqndersfixedOPE0opt :: Floating a => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> a -> a -> FunctionalEls a
combinecrossingeqndersfixedOPE0opt n nd h1 h3 g113sq g113g333 g333sq gapPpZp gapPpZm gapPmZm =
  FunctionalEls
  { constraints =
      [ shift gapPpZp
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn1
        , pvmpolys = [[ polys1    , polys6LHS ]
                     ,[ polys6LHS , polys2    ]]
        }
      , shift gapPpZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (+) polys6RHS polys5 ]]
        }
      , shift gapPmZm
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn5
        , pvmpolys = [[ zipWith (-) polys6RHS polys5 ]]
        }
      ]
    , norm = zipWith (+) normope normid
    , obj = replicate (nd1 + nd2 + nd5 + nd6) 0
  }
  where
    normope = zipWith5 (\x y z u v -> g113sq * (x + y + z) + 2 * g113g333 * u + g333sq * v)
                 norm6RHS norm5 norm1 norm6LHS norm2
    normid = zipWith3 (\x y z -> x + 2 * y + z) identity1 identity6 identity2
    [nd1, nd2, nd5, nd6] = [nd, nd, nd, 2 * nd]
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
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 n
    ceqndsEqn2 = crossingeqndersEqn2 h1 h3 n
    ceqndsEqn5 = crossingeqndersEqn5 h1 h3 n
    ceqndsEqn6LHS = crossingeqndersEqn6LHS h1 h3 n
    ceqndsEqn6RHS = crossingeqndersEqn6RHS h1 h3 n


singlecrossingeqnders :: Floating a => RhoOrder -> Int -> a -> a -> a -> FunctionalEls a
singlecrossingeqnders n nd h1 h3 gap =
  FunctionalEls
  { constraints =
      [ shift gap
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn1
        , pvmpolys = [[ take nd $ polys ceqndsEqn1 ]]
        }
      ]
    , norm = take nd $ ceqndsEqn1 `at` h3
    , obj = take nd $ idty ceqndsEqn1
  }
  where
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 n


singlecrossingeqnders0opt :: Floating a => RhoOrder -> Int -> a -> a -> a -> FunctionalEls a
singlecrossingeqnders0opt n nd h1 h3 gap =
  FunctionalEls
  { constraints =
      [ shift gap
        PolyVectorMatrix {
          pvmpref = pref ceqndsEqn1
        , pvmpolys = [[ take nd $ polys ceqndsEqn1 ]]
        }
        ,
        PolyVectorMatrix {
          -- simple prefactor, used only to get non-trivial bilinearBasis
          pvmpref = dampedRational00 2
        , pvmpolys = [[ take nd $ constP <$> idty ceqndsEqn1 ]]
        }
      ]
    , norm = take nd $ ceqndsEqn1 `at` h3
    , obj = replicate nd 0
  }
  where
    ceqndsEqn1 = crossingeqndersEqn1 h1 h3 n

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
maxOPESDPFull113Z2 nPs nd h1 h3 gapPpZp gapPpZm gapPmZm rat =
  normalize $ combinecrossingeqnders nPs nd h1 h3 rat gapPpZp gapPpZm gapPmZm

maxOPESDPSingle :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> SDP a
maxOPESDPSingle nPs nd h1 h3 gap =
  normalize $ singlecrossingeqnders nPs nd h1 h3 gap

feasibilitySDPSingle :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> SDP a
feasibilitySDPSingle nPs nd h1 h3 gap =
  normalize $ singlecrossingeqnders0opt nPs nd h1 h3 gap

feasibilitySDPFull113Z2 :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> SDP a
feasibilitySDPFull113Z2 nPs nd h1 h3 gapPpZp gapPpZm gapPmZm rat =
  normalize $ combinecrossingeqnders0opt nPs nd h1 h3 rat gapPpZp gapPpZm gapPmZm

feasibilitySDPFull113Z2fixedOPE :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> a -> a -> SDP a
feasibilitySDPFull113Z2fixedOPE nPs nd h1 h3 gapPpZp gapPpZm gapPmZm g113sq g113g333 g333sq =
  normalize $ combinecrossingeqndersfixedOPE0opt nPs nd h1 h3 g113sq g113g333 g333sq gapPpZp gapPpZm gapPmZm

writeSDPtoFile :: (Ord a, Floating a, Show a) => FilePath -> SDP a -> IO ()
writeSDPtoFile fp sdp = writeXMLSDPtoFile fp (optvec sdp) (pvms sdp)
