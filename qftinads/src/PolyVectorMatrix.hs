module PolyVectorMatrix
    ( DampedRational(DampedRational, coeff, poles, expo)
    , PolyVectorMatrix(PolyVectorMatrix, pvmpref, pvmpolys)
    , evaldr
    , shiftdr
    , orthonormalpolysfromdr
    , samplePoints
    -- , bilinearBasis
    -- , samplePoints
    -- , sampleScalings
    ) where

import SimplePoly
import Data.List
import Data.Maybe

data DampedRational a = DampedRational { coeff :: a
                                       , poles :: [a]
                                       , expo :: a
                                       }

data PolyVectorMatrix a = PolyVectorMatrix { pvmpref :: DampedRational a
                                           , pvmpolys :: [[[Poly a]]]
                                           }

type Monomialinnerprods a = [a]


evaldr :: Floating a => DampedRational a -> a -> a
evaldr p h = coeff p * (expo p ** h) / product ((-) h <$> poles p)

shiftdr :: Floating a => a -> DampedRational a -> DampedRational a
shiftdr a dr = DampedRational { coeff = cdr * edr ** a
                              , expo = edr
                              , poles = (\x -> x - a ) <$> psdr
                              }
                              where
                                cdr = coeff dr
                                edr = expo dr
                                psdr = poles dr

nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z : nestmap f z xs

nestmap2 :: (a -> b -> b -> b) -> b -> b -> [a] -> [b]
nestmap2 _ _ _ [] = []
nestmap2 f x y (n:ns) = let z = f n x y in z : nestmap2 f y z ns

partfracnRecs :: Floating a => a -> [a]
partfracnRecs x = zipWith (/) aAs bBs
  where
    aAs = nestmap2 (\ ab x y -> snd ab * y + fst ab * x ) 1 x (zip as bs)
    bBs = nestmap2 (\ ab x y -> snd ab * y + fst ab * x ) 0 1 (zip as bs)
    as = fromInteger <$> concatMap (replicate 2) [1..]
    bs = cycle [1, x]

incompleteGamma0 :: (Eq a, Floating a) => a -> a
incompleteGamma0 x = let pf = fst $ fromJust $ find (uncurry (==)) $ (zip <*> tail . tail) (partfracnRecs x)
                     in exp (-x) / pf

incompleteGamma0approx :: (Eq a, Floating a) => a -> a
incompleteGamma0approx x = exp (-x) * log ((1 + x) ^ 2 * (2 + x) / x^3) / 4

dropEl :: Int -> [a] -> [a]
dropEl n xs = take n xs ++ drop (n+1) xs

fact :: (Integral a, Num b) => a -> b
fact n = fromIntegral $ product [1..n]

int0coeffs :: (Eq a, Floating a) => DampedRational a -> [a]
int0coeffs dr = zipWith (\ p n -> base ** p * incompleteGamma0 (p * lbase)) ps [0..]
  where ps = poles dr
        base = expo dr
        lbase = log base


intcoeffs :: (Eq a, Floating a) => DampedRational a -> [[a]]
intcoeffs dr = int0s : nestmap (\m cs -> (+) (incr m) <$> zipWith (*) ps cs) int0s [0..]
  where ps = poles dr
        lbase = log $ expo dr
        incr m = (- 1/lbase) ^ (m + 1) * fact m
        int0s = int0coeffs dr

intvals :: (Ord a, Eq a, Floating a) => DampedRational a -> Monomialinnerprods a
intvals dr = (\cl -> cf * sum (zipWith (/) cl poleprods)) <$> intcoeffs sdr
  where poleprods = zipWith (\p n -> product ((-) p <$> dropEl n ps)) ps [0..]
        ps = poles sdr
        cf = coeff sdr
        sdr = safe dr

safe :: (Num a, Ord a) => DampedRational a -> DampedRational a
safe dr = dr { poles = [ p | p <- poles dr, p < 0 ] }

innerprod :: Num a => Monomialinnerprods a -> Poly a -> Poly a -> a
innerprod intvals (CL xs) (CL ys) =
  sum $ zipWith fn [[ x * y | x <- xs] | y <- ys] [0..]
  where
    fn row n = sum $ zipWith (*) (drop n safeintvals) row
    safeintvals = intvals ++ repeat undefined

iterate2 :: (a -> a -> a) -> a -> a -> [a]
iterate2 f a b = a : iterate2 f b (f a b)

orthonormalpolys :: Floating a => Monomialinnerprods a -> [Poly a]
orthonormalpolys moninprods = normalize <$> iterate2 nextpol oneP startP
  where
    x = CL [0,1]
    alpha p = constP $ inprod p (x * p) / inprod p p
    beta p q = constP $ inprod p p / inprod q q
    inprod = innerprod moninprods
    normalize p = p * constP (1 / sqrt (inprod p p))
    nextpol q p = (x - alpha p) * p -  beta p q * q
    oneP = constP 1
    startP = x - constP (inprod oneP x / inprod oneP oneP)

orthonormalpolysfromdr :: (Floating a, Eq a, Ord a) => DampedRational a -> [Poly a]
orthonormalpolysfromdr = orthonormalpolys . intvals . safe

samplePoints :: Floating a => DampedRational a -> Int -> [a]
samplePoints dr n = (\k -> pi^2 * (4 * fi k - 1)^2 / (- 64 * fi n * lbase)) <$> [0..(n-1)]
  where fi = fromIntegral
        lbase = log $ expo dr / 4
