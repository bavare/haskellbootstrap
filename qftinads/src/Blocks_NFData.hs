module Blocks_NFData
    ( blockval00
    , blockval
    , RhoOrder
    , numeratorpolys00
    , numeratorpolys
    , denominator00
    , denominator
    -- , blockapprox
    ) where

import SimplePoly
import Numeric.AD
import Data.List
import Data.Maybe
import Control.DeepSeq

type RhoOrder = Int

-- blockapprox :: (Floating a) => a -> a -> a -> RhoOrder -> Int -> a
-- blockapprox a b h n m = eval h (numeratorpolys a b n !! m) / denominator n h
--
-- difference :: (Eq a, Floating a) => a -> a -> a -> RhoOrder -> a
-- difference a b h n = blockval a b h (1/2) - blockapprox a b h n 0

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------
nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z : nestmap f z xs

nestmap2 :: (a -> b -> b -> b) -> b -> b -> [a] -> [b]
nestmap2 _ _ _ [] = []
nestmap2 f x y (n:ns) = let z = f n x y in z : nestmap2 f y z ns

nestmap3 :: (a -> b -> b -> b -> b) -> b -> b -> b -> [a] -> [b]
nestmap3 _ _ _ _ [] = []
nestmap3 f x y z (n:ns) = let w = f n x y z in z : nestmap3 f y z w ns

rho :: (Floating a) => a -> a
rho z = z / (1 + sqrt (1 - z))^2

rhodiffs :: (Floating a) => a -> [a]
rhodiffs = diffs rho

rhotoz :: (Floating a) => Poly a
rhotoz = CL (tail $ zipWith (/) (rhodiffs (1/2)) facts)

-- rhotozdiffs :: (Num a) =>
-- x = getCL $ sum . zipWith (*) (constP <$> rhodiffs) (nestmap (* rhotoz) 1 [1..n])
--------------------------------------------------------------------------------
-- Recursion relations (internal)
--------------------------------------------------------------------------------
hypgrecursion :: (Fractional a) => a -> a -> a -> a -> Integer -> a
hypgrecursion a b c r n = let m = fromIntegral n in r * (a + m) * (b + m) / (c + m) / (m + 1)

blockrecursion :: (Floating a) => a -> a -> a -> a -> a -> a -> a -> Integer -> a
blockrecursion a b h r w1 w2 w3 n = w4
    where w4 = ( r * r * w2 * (2 * h * (2*a + 2*b + nn - 1) - 4 * a * (b - nn + 2) + (nn-2) * (4*b + nn - 1))
               + r * w3 * (2 * h * (2*a + 2*b - nn + 1) + 4 * a * (b + nn - 1) + (nn-1) * (4*b - nn + 2))
               + r * r * r * w1 * (2 * h * (nn-2) + (nn-3) * (nn-2)) ) / nn / (nn + 2 * h - 1)
          nn = fromIntegral n



-- numrecursion :: (NFData a, Floating a) => a -> a -> a -> Poly a -> Poly a -> Poly a -> Integer -> Poly a
-- numrecursion a b r w1 w2 w3 n = w4
--     where w4 = ( w2 * CL [r * r * (- 4 * a * (b - nn + 2) + (nn-2) * (4*b + nn - 1)), r * r * 2 * (2*a + 2*b + nn - 1)]
--                + w3 * CL [r * (4 * a * (b + nn - 1) + (nn-1) * (4*b - nn + 2)), r * 2 * (2*a + 2*b - nn + 1)]
--                + w1 * CL [r * r * r * (nn-3) * (nn-2), r * r * r * 2 * (nn-2)] ) * constP (1 / nn)
--           nn = fromIntegral n

--------------------------------------------------------------------------------
-- List of terms in the series expansion (internal)
--------------------------------------------------------------------------------

hypgtermlist :: (Fractional a) => a -> a -> a -> a -> [a]
hypgtermlist a b c r = 1 : nestmap (\ m w -> w * hypgrecursion a b c r m) 1 [0..]

-- Equivalent but slower and higher memory footprint
-- hypgtermlist' :: (Fractional a) => a -> a -> a -> a -> [a]
-- hypgtermlist' a b c r = 1 : zipWith (\ m w -> w * hypgrecursion a b c r m) [0..] (hypgtermlist' a b c r)

blocktermlist00 :: (Floating a) => a -> a -> [a]
blocktermlist00 h z = let r = rho z in (((4 * r) ** h) *) <$> hypgtermlist (1/2) h (h + 1/2) (r^2)

blocktermlist :: (Floating a) => a -> a -> a -> a -> [a]
blocktermlist a b h z = let r = rho z in nestmap3 (\m w1 w2 w3 -> blockrecursion a b h r w1 w2 w3 m) 0 0 ((4 * r) ** h) [1..]

-- numtermlist :: (NFData a, Floating a) => a -> a -> a -> Integer -> [Poly a]
-- numtermlist a b r n = zipWith (*)
--                             (nestmap3 (\m w1 w2 w3 -> numrecursion a b r w1 w2 w3 m) (constP 0) (constP 0) (constP 1) [1..n])
--                             [pochhammer (CL [fromIntegral m, 2]) (2 * n - 2 * m) | m <- [1..n] ]


--------------------------------------------------------------------------------
-- Get the actual value of a block
--------------------------------------------------------------------------------

evaluateterms :: (Eq a, Num a) => [a] -> a
evaluateterms termlist = let partialsums = nestmap (+) 0 termlist
                         in fst $ fromJust $ find (uncurry (==)) $ (zip <*> tail . tail) partialsums

hypgval a b c r = evaluateterms $ hypgtermlist a b c r
blockval00 h z = evaluateterms $ blocktermlist00 h z
blockval a b h z = evaluateterms $ blocktermlist a b h z

--------------------------------------------------------------------------------
-- Compute z-derivatives at 1/2 using automatic differentiation (Numeric.AD)
--------------------------------------------------------------------------------

diffsblock00 :: (Floating a, NFData a) => RhoOrder -> a -> [a]
diffsblock00 n h = diffs (sum . take ((n `quot` 2) + 1) . blocktermlist00 (auto h)) (fromRational (1/2))

diffsblock :: (NFData a, Floating a) => a -> a -> RhoOrder -> a -> [a]
diffsblock a b n h = diffs (sum . take (n+1) . blocktermlist (auto a) (auto b) (auto h)) (fromRational (1/2))

--------------------------------------------------------------------------------
-- Rational approximation: denominators
--------------------------------------------------------------------------------

denominator00 :: (Floating a) => RhoOrder -> a -> a
denominator00 n h = (4 * r) ** (-h) * poles
                    where
                       r = rho (fromRational (1/2))
                       poles = product [ 2 * h + 2 * fromIntegral j - 1 | j <- [1..n `quot` 2] ]

-- denominator :: (NFData a, Floating a) => RhoOrder -> a -> a
-- denominator n h = (4 * r) ** (-h) * poles
--                   where
--                      r = rho (fromRational (1/2))
--                      poles = product [ 2 * h + 2 * fromIntegral j - 1 | j <- [1..n `quot` 2] ]
--                              * product [ 2 * h + 2 * fromIntegral j - 2 | j <- [1..((n + 1) `quot` 2)] ]

denominator :: (NFData a, Floating a) => RhoOrder -> a -> a
denominator n h = (4 * r) ** (-h) * poles
                  where
                    r = rho (fromRational (1/2))
                    poles = pochhammer (2 * h) n


pochhammer :: (NFData a, Num a, Integral b) => a -> b -> a
pochhammer h n = product [ h + fromIntegral m | m <- [0..(n-1)] ]

fact :: (Integral a, Num b) => a -> b
fact n = fromIntegral $ product [1..n]

facts :: (Num a) => [a]
facts = fromIntegral <$> 1 : nestmap (*) 1 [1..]



--------------------------------------------------------------------------------
-- Rational approximation: numerators as polys
--------------------------------------------------------------------------------

numerators00 :: (NFData a, Floating a) => RhoOrder -> a -> [a]
numerators00 n h = (denominator00 n h *) <$> diffsblock00 n h

numerators :: (NFData a, Floating a) => a -> a -> RhoOrder -> a -> [a]
numerators a b n h = (denominator n h *) <$> diffsblock a b n h

numeratorpolys00 :: (NFData a, Floating a) => RhoOrder -> [Poly a]
numeratorpolys00 n = sampsToPoly <$>
                     -- For the m'th derivative the degree of polynomial is nt + m so we take that many elements:
                     zipWith take [(n `quot` 2 + 1)..]
                     (zip samplepoints <$> transpose (numerators00 n <$> samplepoints))
                     where
                        -- In principle arbitrary, chosen midway between the zeroes and then some
                        samplepoints = [ - 2 * fromIntegral j | j <- [1..] ]

numeratorpolys :: (NFData a, Floating a) => a -> a -> RhoOrder -> [Poly a]
numeratorpolys a b n =  sampsToPoly <$>
                        -- For the m'th derivative the degree of polynomial is nt + m so we take that many elements:
                        zipWith take [n+1..]
                        (zip samplepoints <$> transpose (numerators a b n <$> samplepoints))
                        where
                          -- In principle arbitrary, chosen midway between the zeroes and then some
                          samplepoints = [ - fromIntegral j / 2 + 1 / 4  | j <- [1..] ]

-- numeratorpolysDEB :: (NFData a, Floating a) => a -> a -> RhoOrder -> [Poly a]
numeratorpolysDEB a b n = -- For the m'th derivative the degree of polynomial is nt + m so we take that many elements:
                        zipWith take [n+1..]
                        (zip samplepoints <$> transpose (numerators a b n <$> samplepoints))
                        where
                          -- In principle arbitrary, chosen midway between the zeroes and then some
                          samplepoints = [ - fromIntegral j / 2 + 1 / 4  | j <- [1..] ]


numeratorpolysDEB' a b n = -- For the m'th derivative the degree of polynomial is nt + m so we take that many elements:
                        zipWith take [n+1..]
                        (zip samplepoints <$> transpose (numerators a b n <$> samplepoints))
                        where
                          -- In principle arbitrary, chosen midway between the zeroes and then some
                          samplepoints = [ - fromIntegral j / 2 + 1 / 4  | j <- [1..] ]
