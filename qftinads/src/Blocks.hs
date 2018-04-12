module Blocks
    (
    -- blockval00
    -- , blockval
    -- ,
    RhoOrder
    , numeratorpolys00
    , numeratorpolys
    , numeratordiffs
    , prefactordiffs
    , numeratordiffs00
    , denominator00
    , denominator
    , rhotoz
    ) where

import SimplePoly
import Numeric.AD
import Data.List

type RhoOrder = Integer

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z : nestmap f z xs

nestmap3 :: (a -> b -> b -> b -> b) -> b -> b -> b -> [a] -> [b]
nestmap3 _ _ _ _ [] = []
nestmap3 f x y z (n:ns) = let w = f n x y z in z : nestmap3 f y z w ns

crossdiagonalsums :: Num a => [[a]] -> [a]
crossdiagonalsums (x:xs) =
  zipWith (+) (x ++ take (length xs) (map fromInteger [0,0..])) (0:crossdiagonalsums xs)
crossdiagonalsums [] = map fromInteger [0,0..]

binomialstab :: Num a => [[a]]
binomialstab = binomialsrows $ map fromInteger [1,1..]
  where binomialsrows r = r : binomialsrows (nestmap (+) 0 r)

-- takes two lists, [f, f', f'', f''', ...] and  [g, g', g'', g''', ...]
-- and returns [fg, (fg)', (fg)'', (fg)''', ...]
productrule :: Num a => [a] -> [a] -> [a]
productrule ds es =
  crossdiagonalsums $ zipWith (zipWith (*)) diffstab binomialstab
  where
    diffstab = [ [ d * e | d <- ds ] | e <- es ]

--------------------------------------------------------------------------------
-- Elementary functions
--------------------------------------------------------------------------------

fact :: (Integral a, Num b) => a -> b
fact n = fromIntegral $ product [1..n]

facts :: (Num a) => [a]
facts = fromIntegral <$> 1 : nestmap (*) 1 [1..]

pochhammer :: (Num a, Integral b) => a -> b -> a
pochhammer h n = product [ h + fromIntegral m | m <- [0..(n-1)] ]

rho :: (Floating a) => a -> a
rho z = z / (1 + sqrt (1 - z))^2

--------------------------------------------------------------------------------
-- Numerator diff polynomials
--------------------------------------------------------------------------------

numrecursion :: (Floating a) => a -> a -> a -> Integer -> Poly a -> Poly a -> Poly a -> Poly a
numrecursion a b r 1 _ _ w3 = w4
    where w4 = ( w3 * CL [ (2 + 4 * b - nn) * (nn - 1) + 4 * a * (nn + b - 1)
                         , 2 + 4 * a + 4 * b - 2 * nn
                         ] * constP r
               ) * constP (1/nn)
          nn = 1
numrecursion a b r 2 _ w2 w3 = w4
    where w4 = ( w3 * CL [ (2 + 4 * b - nn) * (nn - 1) + 4 * a * (nn + b - 1)
                         , 2 + 4 * a + 4 * b - 2 * nn
                         ] * constP r
               + w2 * CL [ (nn - 2) * ((nn - 2) * (4 * b + nn - 1) - 4 * a * (2 + b - nn))
                         , -4 * ( a * (6 + 2 * b - 3 * nn) - (nn - 2) * (3 * b + nn - 1))
                         , 4 * (2 * a + 2 * b + nn - 1)
                         ] * constP (r ^ 2)
               ) * constP (1/nn)
          nn = 2
numrecursion a b r n w1 w2 w3 = w4
    where w4 = ( w3 * CL [ (2 + 4 * b - nn) * (nn - 1) + 4 * a * (nn + b - 1)
                         , 2 + 4 * a + 4 * b - 2 * nn
                         ] * constP r
               + w2 * CL [ (nn - 2) * ((nn - 2) * (4 * b + nn - 1) - 4 * a * (2 + b - nn))
                         , -4 * ( a * (6 + 2 * b - 3 * nn) - (nn - 2) * (3 * b + nn - 1))
                         , 4 * (2 * a + 2 * b + nn - 1)
                         ] * constP (r ^ 2)
               + w1 * CL [ (6 - 5 * nn + nn^2) ^ 2
                         , 2 * (nn - 3) * (nn - 2) * (3 * nn - 7)
                         , 4 * (nn - 2) * (3 * nn - 8)
                         , 8 * (nn - 2)
                         ] * constP (r ^ 3)
                ) * constP (1 / nn)
          nn = fromIntegral n

numrecursion00 :: (Floating a) => a -> Integer -> Poly a -> Poly a
numrecursion00 r n w1 = w1 * constP ((1 + 2 * nn) * (r^2) / (2 * (nn + 1))) * CL [nn, 1]
  where nn = fromIntegral n

numerator00 :: (Floating a) => a -> RhoOrder -> Poly a
numerator00 r n = sum $ zipWith (*)
                          (constP 1 : nestmap (numrecursion00 r) (constP 1) [0..nhf])
                          [pochhammer (CL [fromIntegral m + 1/2, 1]) (nhf - m) | m <- [0..nhf] ]
                  where nhf = n `quot` 2

numerator :: (Floating a) => a -> a -> a -> RhoOrder -> Poly a
numerator a b r n = sum $ zipWith (*)
                            (nestmap3 (numrecursion a b r) (constP 0) (constP 0) (constP 1) [1..(n+1)])
                            [pochhammer (CL [fromIntegral m, 2]) (n - m) | m <- [0..n] ]

numeratordiffs :: (Floating a) => a -> a -> RhoOrder -> [Poly a]
numeratordiffs a b n = let diffslist = diffs0F (\x -> numerator (auto a) (auto b) x (auto n)) (rho (1/2))
                       -- diffsF returns Poly [a] but we need [Poly a], so:
                       in CL <$> transpose (getCL diffslist)

numeratordiffs00 :: (Floating a) => RhoOrder -> [Poly a]
numeratordiffs00 n = let diffslist = diffs0F (\x -> numerator00 x (auto n)) (rho (1/2))
                     -- diffsF returns Poly [a] but we need [Poly a], so:
                     in CL <$> transpose (getCL diffslist)

prefactordiffs :: (Floating a) => [Poly a]
prefactordiffs = [ pref n * pochhammer (CL [1 - fi n, 1]) n | n <- [0..] ]
                 where
                    fi = fromInteger
                    pref n = constP (rho (1/2) ** (- fi n))

numeratorpolys :: (Floating a) => a -> a -> RhoOrder -> [Poly a]
numeratorpolys a b n = (\r -> sum $ zipWith (.*) r blockrhodiffs) <$> rhotoz
  where
    -- numeratordiffs gets called only once
    blockrhodiffs = productrule prefactordiffs (numeratordiffs a b n)
    (.*) coeff poly = constP coeff * poly

numeratorpolys00 :: (Floating a) => RhoOrder -> [Poly a]
numeratorpolys00 n = (\r -> sum $ zipWith (.*) r blockrhodiffs) <$> rhotoz
  where
    -- numeratordiffs gets called only once
    blockrhodiffs = productrule prefactordiffs (numeratordiffs00 n)
    (.*) coeff poly = constP coeff * poly


rhotoz' :: (Floating a) => [[a]]
rhotoz' = zipWith take [1..] (transpose rhotozfactmatrix)
  where
    rhotozfactmatrix = zipWith (zipWith (*)) rhotozmatrix factmatrix
    factmatrix = [ [ fact m / fact n | m <- [0..] ] | n <- [0..] ]
    rhotozmatrix = [ getCL (rhotoztaylor ^ n) ++ repeat 0 | n <- [0..] ]
      where
        rhotoztaylor = CL (zipWith (/) (diffs rho (1/2)) facts) - CL [rho (1/2)]

rhotoz :: (Floating a) => [[a]]
rhotoz = zipWith take [1..] (transpose rhotozfactmatrix)
  where
    rhotozfactmatrix = zipWith (zipWith (*)) (getCL <$> rhotozmatrix) factmatrix
    factmatrix = [ [ fact m / fact n | m <- [0..] ] | n <- [0..] ]
    rhotozmatrix = iterate (* rhotoztaylor) (CL (1 : repeat 0))
      where
        rhotoztaylor = CL (zipWith (/) (diffs rho (1/2)) facts) - CL [rho (1/2)]


--------------------------------------------------------------------------------
-- Denominator
--------------------------------------------------------------------------------

denominator :: Floating a => RhoOrder -> a -> a
denominator n h = (4 * r) ** (-h) * poles
                  where
                    r = rho (1/2)
                    poles = pochhammer (2 * h) n


denominator00 :: Floating a => RhoOrder -> a -> a
denominator00 n h = (4 * r) ** (-h) * poles
                    where
                      r = rho (1/2)
                      poles = pochhammer (1/2 + h) (n `quot` 2)
