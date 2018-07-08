{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}

module Functionals
 ( writeSDPtoFile
 , maxOPESDPSimple
 , feasibilitySDPSimple
 , maxOPESDPFull113Even
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

data Functional a = Functional { f1 :: [Poly a]
                               , f1Id :: [a]
                               , f2 :: [Poly a]
                               , f2Id :: [a]
                               , f3 :: [Poly a]
                               , f4 :: [Poly a]
                               , f5 :: [Poly a]
                               , f6 :: [Poly a]
                               , f6Id :: [a]
                               , g6 :: [Poly a]
                               , den :: a -> a
                               , h1 :: a
                               , h3 :: a
                               }
                               deriving (Generic, NFData)
type InfiniteFunctionalFns a = Functional a
type FiniteFunctionalFns a = Functional a
type VectorFunctional a = Functional a
type NormalizedVectorFunctional a = Functional a

newtype Matrix a = MT { getEls :: [[a]] } deriving (Functor, Show, Generic, NFData)
type PolyVectorMatrix a = Matrix [Poly a]

data SDP a = SDP { pvms :: [PolyVectorMatrix a], optvec :: [a] } deriving (Generic, NFData)

nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z : nestmap f z xs

-- takes two lists, [f, f', f'', f''', ...] and  [g, g', g'', g''', ...]
-- and returns [fg, (fg)', (fg)'', (fg)''', ...]
productrule :: Num a => [a] -> [a] -> [a]
productrule ds es =
  crossdiagonalsums $ zipWith (zipWith (*)) diffstab binomialstab
  where
    diffstab = [ [ d * e | d <- ds ] | e <- es ]

binomialstab :: Num a => [[a]]
binomialstab = binomialsrows $ map fromInteger [1,1..]
  where binomialsrows r = r : binomialsrows (nestmap (+) 0 r)

crossdiagonalsums :: Num a => [[a]] -> [a]
crossdiagonalsums (x:xs) =
  zipWith (+) (x ++ take (length xs) (map fromInteger [0,0..])) (0:crossdiagonalsums xs)
crossdiagonalsums [] = map fromInteger [0,0..]

functionalFns :: (Floating a) => a -> a -> RhoOrder -> InfiniteFunctionalFns a
functionalFns h1 h3 n =
  Functional
  { f1 = onlyOdds $ addfactden $ productrule
            (map constP (diffs (\x -> 2 * (1-x) ** (2 * auto h1)) (1/2)))
            nps00
  , f1Id = onlyOdds $ addfactdenId $ productrule
            (diffs (\x -> 2 * (1-x) ** (2 * auto h1)) (1/2))
            (1 : repeat 0)
  , f2 = onlyOdds $ addfactden $ productrule
            (map constP (diffs (\x -> 2 * (1-x) ** (2 * auto h3)) (1/2)))
            nps00
  , f2Id = onlyOdds $ addfactdenId $ productrule
            (diffs (\x -> 2 * (1-x) ** (2 * auto h3)) (1/2))
            (1 : repeat 0)
  , f3 = zipWith (-)
         (addfactden $ productrule
            (map constP (diffs (\x -> (1-x) ** (2 * auto h3)) (1/2)))
            nps0h31)
         (signAlternate $ addfactden $ productrule
            (map constP (diffs (\x -> (1-x) ** (2 * auto h3)) (1/2)))
            nps0h13)
            -- TODO: delete identically zero polynomials which appear when h1 = h3
  , f4 = zipWith (-)
         (addfactden $ productrule
            (map constP (diffs (\x -> (1-x) ** (2 * auto h1)) (1/2)))
            nps0h13)
         (signAlternate $ addfactden $ productrule
            (map constP (diffs (\x -> (1-x) ** (2 * auto h1)) (1/2)))
            nps0h31)
            -- TODO: delete identically zero polynomials which appear when h1 = h3
  , f5 = onlyOdds $ addfactden $ productrule
            (map constP (diffs (\x -> 2 * (1-x) ** (auto h1 + auto h3)) (1/2)))
            npsh13h31
  , f6 = addfactden $ productrule
            (map constP (diffs (\x -> (1/2) * (1-x) ** (auto h1 + auto h3)) (1/2)))
            nps00
  , f6Id = addfactdenId $ productrule
            (diffs (\x -> (1/2) * (1-x) ** (auto h1 + auto h3)) (1/2))
            (1 : repeat 0)
  , g6 = signAlternate $ addfactden $ productrule
            (map constP (diffs (\x -> (-1) * (1-x) ** (2 * auto h3)) (1/2)))
            npsh31h31
  , den = denominator n
  , h1 = h1
  , h3 = h3
  }
  where
    -- onlyOdds :: [a] -> [a]
    onlyOdds (x:y:xs) = y : onlyOdds xs
    onlyOdds _ = []
    -- onlyEvens :: [a] -> [a]
    onlyEvens (x:y:xs) = x : onlyEvens xs
    onlyEvens x = x
    -- signAlternate :: (Num a) => [a] -> [a]
    signAlternate (x:y:xs) = x:(-y):signAlternate xs
    signAlternate x = x
    -- inverseFacts :: (Floating a) => [a]
    inverseFacts = scanl (/) 1 (fromInteger <$> [1..])
    addfactden = zipWith (*) (constP <$> inverseFacts)
    addfactdenId =  zipWith (*) inverseFacts
    nps00 = numeratorpolys 0 0 n
    nps0h13 = numeratorpolys 0 (h1 - h3) n
    nps0h31 = numeratorpolys 0 (h3 - h1) n
    npsh13h31 = numeratorpolys (h1 - h3) (h3 - h1) n
    npsh31h31 = numeratorpolys (h3 - h1) (h3 - h1) n

rescaleat :: (Floating a, Eq a) => a -> InfiniteFunctionalFns a -> InfiniteFunctionalFns a
rescaleat h fns =
  Functional
  { f1 = zipWith (/.) (f1 fns) f1cs
  , f1Id = zipWith (/) (f1Id fns) f1cs
  , f2 = zipWith (/.) (f2 fns) f2cs
  , f2Id = zipWith (/) (f2Id fns) f2cs
  , f3 = zipWith (/.) (f3 fns) f3cs
  , f4 = zipWith (/.) (f4 fns) f4cs
  , f5 = zipWith (/.) (f5 fns) f5cs
  , f6 = zipWith (/.) (f6 fns) f6cs
  , f6Id = zipWith (/) (f6Id fns) f6cs
  , g6 = zipWith (/.) (g6 fns) f6cs
  , den = den fns
  , h1 = h1 fns
  , h3 = h3 fns
  }
  where
    (/.) p x = p * constP (1/x)
    f1cs = zeroestoones . eval h <$> f1 fns
    f2cs = zeroestoones . eval h <$> f2 fns
    f3cs = zeroestoones . eval h <$> f3 fns
    f4cs = zeroestoones . eval h <$> f4 fns
    f5cs = zeroestoones . eval h <$> f5 fns
    f6cs = zeroestoones . eval h <$> f6 fns
    zeroestoones 0 = 1
    zeroestoones x = x

functionalFnsSimple :: (Floating a) => a -> RhoOrder -> InfiniteFunctionalFns a
functionalFnsSimple h1 n =
  Functional
  { f1 = onlyOdds $ addfactden $ productrule
            (map constP (diffs (\x -> 2 * (1-x) ** (2 * auto h1)) (1/2)))
            (numeratorpolys00 n)
  , f1Id = onlyOdds $ addfactdenId $ productrule
            (diffs (\x -> 2 * (1-x) ** (2 * auto h1)) (1/2))
            (1 : repeat 0)
  , f2 = []
  , f2Id = []
  , f3 = []
  , f4 = []
  , f5 = []
  , f6 = []
  , f6Id = []
  , g6 = []
  , den = denominator00 n
  , h1 = h1
  , h3 = undefined
  }
  where
    -- onlyOdds :: [a] -> [a]
    onlyOdds (x:y:xs) = y : onlyOdds xs
    onlyOdds _ = []
    -- onlyEvens :: [a] -> [a]
    onlyEvens (x:y:xs) = x : onlyEvens xs
    onlyEvens x = x
    -- signAlternate :: (Num a) => [a] -> [a]
    signAlternate (x:y:xs) = x:(-y):signAlternate xs
    signAlternate x = x
    -- inverseFacts :: (Floating a) => [a]
    inverseFacts = scanl (/) 1 (fromInteger <$> [1..])
    addfactden = zipWith (*) (constP <$> inverseFacts)
    addfactdenId =  zipWith (*) inverseFacts

takeNumDer :: Int -> InfiniteFunctionalFns a -> FiniteFunctionalFns a
takeNumDer nd fns =
  fns
  { f1 = take nd (f1 fns)
  , f1Id = take nd (f1Id fns)
  , f2 = take nd (f2 fns)
  , f2Id = take nd (f2Id fns)
  , f3 = take (quot nd 2) (f3 fns)
  , f4 = take (quot nd 2) (f4 fns)
  , f5 = take nd (f5 fns)
  , f6 = take (quot nd 2) (f6 fns)
  , f6Id = take (quot nd 2) (f6Id fns)
  , g6 = take (quot nd 2) (g6 fns)
  }

takeNumDerZ2 :: Int -> InfiniteFunctionalFns a -> FiniteFunctionalFns a
takeNumDerZ2 nd fns =
  fns
  { f1 = take nd (f1 fns)
  , f1Id = take nd (f1Id fns)
  , f2 = take nd (f2 fns)
  , f2Id = take nd (f2Id fns)
  , f3 = []
  , f4 = []
  , f5 = take nd (f5 fns)
  , f6 = take (quot nd 2) (f6 fns)
  , f6Id = take (quot nd 2) (f6Id fns)
  , g6 = take (quot nd 2) (g6 fns)
  }

takeNumDerSimple :: Int -> InfiniteFunctionalFns a -> FiniteFunctionalFns a
takeNumDerSimple nd fns =
  fns
  { f1 = take nd (f1 fns)
  , f1Id = take nd (f1Id fns)
  }

dropEl :: Int -> [a] -> [a]
dropEl n xs = take n xs ++ drop (n+1) xs

normalize :: (Floating a, Ord a, Num b) => (a -> b) -> [a] -> [b] -> [b]
normalize to normvec polyvec =
  poly : dropEl maxloc (zipWith (\p n -> p - poly * to n) polyvec normvec)
  where
    (maxloc, maxval) = findExtr normvec
    poly = polyvec !! maxloc * to (1 / maxval)

findExtr :: (Num a, Ord a) => [a] -> (Int, a)
findExtr (x:xs) = findExtrRec xs x 0 1

findExtrRec :: (Num a, Ord a) => [a] -> a -> Int -> Int -> (Int, a)
findExtrRec [] prevMax prevPos curPos = (prevPos, prevMax)
findExtrRec (x:xs) prevMax prevPos curPos
  | abs x > abs prevMax = findExtrRec xs x curPos (curPos + 1)
  | otherwise           = findExtrRec xs prevMax prevPos (curPos + 1)

toFunctionalVecs :: (Num a) => FiniteFunctionalFns a -> VectorFunctional a
toFunctionalVecs fns =
  fns
  { f1 = f1 fns ++ zeroarr (l2 + l3 + l4 + l5 + l6)
  , f1Id = f1Id fns ++ zeroarr (l2 + l3 + l4 + l5 + l6)
  , f2 = zeroarr l1 ++ f2 fns ++ zeroarr (l3 + l4 + l5 + l6)
  , f2Id = zeroarr l1 ++ f2Id fns ++ zeroarr (l3 + l4 + l5 + l6)
  , f3 = zeroarr (l1 + l2) ++ f3 fns ++ zeroarr (l4 + l5 + l6)
  , f4 = zeroarr (l1 + l2 + l3) ++ f4 fns ++ zeroarr (l5 + l6)
  , f5 = zeroarr (l1 + l2 + l3 + l4) ++ f5 fns  ++ zeroarr l6
  , f6 = zeroarr (l1 + l2 + l3 + l4 + l5) ++ f6 fns
  , f6Id = zeroarr (l1 + l2 + l3 + l4 + l5) ++ f6Id fns
  , g6 = zeroarr (l1 + l2 + l3 + l4 + l5) ++ g6 fns
  }
  where
    [l1,l2,l3,l4,l5,l6] = map (\f -> length (f fns)) [f1, f2, f3, f4, f5, f6]
    zeroarr n = replicate n 0

pvmMultiParticlesSimple :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesSimple gap fn =
  MT [[ shiftPoly gap <$> f1 fn ]]

pvmMultiParticlesEven :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesEven gap fn =
  MT [[f1s , f4s                 , f6s ]
     ,[f4s , zipWith (+) g6s f5s , f3s ]
     ,[f6s , f3s                 , f2s ]]
  where
    [f1s,f2s,f3s,f4s,f5s,f6s,g6s] =
      (\f -> shiftPoly gap <$> f fn) <$> [f1,f2,f3,f4,f5,f6,g6]

pvmMultiParticlesOdd :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesOdd gap fn =
  MT [[shiftPoly gap <$> zipWith (-) (g6 fn) (f5 fn)]]

-- First 'odd' is parity, second is Z2
pvmMultiParticlesPoddZodd :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesPoddZodd = pvmMultiParticlesOdd

pvmMultiParticlesPevenZodd :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesPevenZodd gap fn =
  MT [[shiftPoly gap <$> zipWith (+) (g6 fn) (f5 fn)]]

pvmMultiParticlesPevenZeven :: (Num a) => a -> VectorFunctional a -> PolyVectorMatrix a
pvmMultiParticlesPevenZeven gap fn =
  MT [[f1s , f6s ]
     ,[f6s , f2s ]]
  where
    [f1s,f2s,f6s] =
      (\f -> shiftPoly gap <$> f fn) <$> [f1,f2,f6]

pvmSingleParticlesBound :: (Fractional a, Num a) => VectorFunctional a -> PolyVectorMatrix a
pvmSingleParticlesBound fn =
  MT [[ f11  , f41              , f61              , zero ]
     ,[ f41  , add3 g61 f51 f13 , add2 f31 f43     , f63  ]
     ,[ f61  , add2 f31 f43     , add3 f21 g63 f53 , f33  ]
     ,[ zero , f63              , f33              , f23  ]]
  where
    evalh1 poly = constP $ eval (h1 fn) poly / den fn (h1 fn)
    evalh3 poly = constP $ eval (h3 fn) poly / den fn (h3 fn)
    zero = constP <$> replicate (length (f1 fn)) 0
    add2 = zipWith (+)
    add3 = zipWith3 (\ a b c -> a + b + c )
    -- first index up, second index down
    -- (todo: use unicode super/subscripts)
    f11 = evalh1 <$> f1 fn
    f21 = evalh1 <$> f2 fn
    f31 = evalh1 <$> f3 fn
    f41 = evalh1 <$> f4 fn
    f51 = evalh1 <$> f5 fn
    f61 = evalh1 <$> f6 fn
    g61 = evalh1 <$> g6 fn
    f13 = evalh3 <$> f1 fn
    f23 = evalh3 <$> f2 fn
    f33 = evalh3 <$> f3 fn
    f43 = evalh3 <$> f4 fn
    f53 = evalh3 <$> f5 fn
    f63 = evalh3 <$> f6 fn
    g63 = evalh3 <$> g6 fn

singleParticlesOptEven :: (Fractional a, Num a) => VectorFunctional a -> a -> [a]
singleParticlesOptEven fn rat =
  add5 g61 f51 f13 ((2 * rat *) <$> f63) ((rat^2 *) <$> f23)
  where
    evalh1 poly = eval (h1 fn) poly / den fn (h1 fn)
    evalh3 poly = eval (h3 fn) poly / den fn (h3 fn)
    zero = constP <$> replicate (length (f1 fn)) 0
    add2 = zipWith (+)
    add5 = zipWith5 (\ a b c d e -> a + b + c + d + e)
    -- first index up, second index down
    -- (todo: use unicode super/subscripts)
    f11 = evalh1 <$> f1 fn
    f21 = evalh1 <$> f2 fn
    f31 = evalh1 <$> f3 fn
    f41 = evalh1 <$> f4 fn
    f51 = evalh1 <$> f5 fn
    f61 = evalh1 <$> f6 fn
    g61 = evalh1 <$> g6 fn
    f13 = evalh3 <$> f1 fn
    f23 = evalh3 <$> f2 fn
    f33 = evalh3 <$> f3 fn
    f43 = evalh3 <$> f4 fn
    f53 = evalh3 <$> f5 fn
    f63 = evalh3 <$> f6 fn
    g63 = evalh3 <$> g6 fn

vecIdMult :: (Floating a, Num a) => VectorFunctional a -> [a]
vecIdMult fn =
  zipWith3 (\ a b c -> (a + 2 * b + c)) (f1Id fn) (f6Id fn) (f2Id fn)

feasibilitySDPSimple :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> SDP a
feasibilitySDPSimple rhoOrder derOrder h1 gap =
  -- SDP { pvms = [ pvmSingleParticlesCont gap fn ]
  --     , optvec = vecId fn
  --     -- , optvec = normVec $ replicate (length (f1 fn)) 1
  --     }
  SDP { pvms = [ normPoly <$> pvmMultiParticlesSimple gap fn ]
      , optvec = normVec $ replicate (length (f1 fn)) 0
      }
  where
    fn =
      toFunctionalVecs $
      takeNumDerSimple derOrder $
      functionalFnsSimple h1 rhoOrder
    normPoly = normalize constP (f1Id fn)
    normVec = normalize id (f1Id fn)

maxOPESDPSimple :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> SDP a
maxOPESDPSimple !rhoOrder !derOrder !h1 !gap !hint =
  SDP { pvms = [ doNormPoly <$> pvmMultiParticlesSimple gap fn ]
      , optvec = doNormVec $ f1Id fn
      }
  where
    fn =
      toFunctionalVecs $
      takeNumDerSimple derOrder $
      functionalFnsSimple h1 rhoOrder
    doNormPoly = normalize constP normvec
    doNormVec = normalize id normvec
    normvec = (\x -> eval hint x / den fn hint) <$> f1 fn

feasibilitySDPfull :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> SDP a
feasibilitySDPfull rhoOrder derOrder h1 h3 evenGap oddGap =
  SDP { pvms = [ doNormPoly <$> pvmMultiParticlesEven evenGap fn,
                 doNormPoly <$> pvmMultiParticlesOdd oddGap fn,
                 doNormPoly <$> pvmSingleParticlesBound fn ]
      , optvec = doNormVec $ replicate (length (f1 fn)) 0
      }
  where
    fn =
      toFunctionalVecs $
      takeNumDer derOrder $
      functionalFns h1 h3 rhoOrder
    doNormPoly = normalize constP normvec
    doNormVec = normalize id normvec
    normvec = vecIdMult fn

maxOPESDPFull113Even :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> SDP a
maxOPESDPFull113Even rhoOrder derOrder h1 h3 evenGap oddGap rat =
  SDP { pvms = [ doNormPoly <$> pvmMultiParticlesEven evenGap fn,
                 doNormPoly <$> pvmMultiParticlesOdd oddGap fn ]
      , optvec = doNormVec $ vecIdMult fn
      }
  where
    fn =
      toFunctionalVecs $
      takeNumDer derOrder $
      rescaleat (2 * h1) $
      functionalFns h1 h3 rhoOrder
    doNormPoly = normalize constP normvec
    doNormVec = normalize id normvec
    normvec = singleParticlesOptEven fn rat

maxOPESDPFull113Z2 :: (Ord a, Floating a) => RhoOrder -> Int -> a -> a -> a -> a -> a -> a -> SDP a
maxOPESDPFull113Z2 rhoOrder derOrder h1 h3 gapPevenZeven gapPevenZodd gapPoddZodd rat =
  SDP { pvms = [ doNormPoly <$> pvmMultiParticlesPevenZeven gapPevenZeven fn,
                 doNormPoly <$> pvmMultiParticlesPevenZodd gapPevenZodd fn,
                 doNormPoly <$> pvmMultiParticlesPoddZodd gapPoddZodd fn ]
      , optvec = doNormVec $ vecIdMult fn
      }
  where
    fn =
      toFunctionalVecs $
      takeNumDerZ2 derOrder $
      rescaleat (2 * h1) $
      functionalFns h1 h3 rhoOrder
    doNormPoly = normalize constP normvec
    doNormVec = normalize id normvec
    normvec = singleParticlesOptEven fn rat

writeSDPtoFile :: (Floating a, Show a) => FilePath -> SDP a -> IO ()
writeSDPtoFile fp sdp = writeXMLSDPtoFile fp (optvec sdp) (getEls <$> pvms sdp)
