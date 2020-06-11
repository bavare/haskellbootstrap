{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module SimplePoly
  ( Poly(CL)
  , Algebra
  , (.*)
  , getCL
  , constP
  , padtodeg
  , deg
  , eval
  , shiftPoly
  , sampsToPoly
  , diffPoly
  , multarg
  , crossdiagonalsums
  ) where

import GHC.Generics (Generic)
import Control.DeepSeq
import Numeric.Rounded

newtype Poly a = CL { getCL :: [a] } deriving (Generic, NFData)

instance (Show a) => Show (Poly a) where
  show (CL (p:ps)) = show p ++ concat (zipWith (\c n -> " + " ++ show c ++ " x^" ++ show n) ps [1..])

deg :: Poly a -> Int
deg (CL p) = length p - 1

padtodeg :: (Num a) => Int -> Poly a -> Poly a
padtodeg n (CL p) = CL (p ++ take (n - length p + 1) (fromInteger <$> [0,0..]))

instance (Num a) => Num (Poly a) where
  (+) = add
  (*) = mult
  fromInteger a = CL [fromInteger a]
  negate (CL p) = CL (map negate p)
  signum = undefined
  abs = undefined

class (Num a, Num b) => Algebra a b where
  (.*) :: a -> b -> b

instance (Num a) => Algebra a (Poly a) where
  (.*) x p = p * constP x

instance (Num a) => Algebra a a where
  (.*) = (*)

-- (.*) :: (Num a) =>  a -> Poly a -> Poly a
-- (.*) x p = p * constP x
--
-- (/.) :: (Floating a) => Poly a -> a -> Poly a
-- (/.) p x = p * constP (recip x)

instance Functor Poly where
  fmap f p = CL (f <$> getCL p)

-- instance (Fractional a) => Fractional (Poly a) where
--     fromRational a = CL [fromRational a]
--     recip (CL [a]) = CL [1/a]
--     recip _        = undefined

-- instance (Floating a) => Floating (Poly a) where
--     pi = CL [pi]
--     exp = undefined
--     log = undefined
--     sin = undefined
--     cos = undefined
--     asin = undefined
--     acos = undefined
--     atan = undefined
--     sinh = undefined
--     cosh = undefined
--     asinh = undefined
--     acosh = undefined
--     atanh = undefined

add :: (Num a) => Poly a -> Poly a -> Poly a
add (CL ((!p):ps)) (CL ((!q):qs)) = CL (p + q : psqs) where psqs = getCL $ CL ps + CL qs
add p (CL []) = p
add (CL []) p = p

-- mult :: (Num a) => Poly a -> Poly a -> Poly a
-- mult (CL ((!p):ps)) (CL ((!q):qs)) = CL ((p*q) : psqs) where psqs = getCL $ CL [p] * CL qs + CL ps * CL (q:qs)
-- -- mult (CL ((!p):ps)) (CL ((!q):qs)) = CL ((p*q) : psqs) where psqs = getCL $ CL ((p *) <$> qs) + CL ps * CL (q:qs)
-- mult _ _ = CL []

-- crossdiagonalsums :: Num a => [[a]] -> [a]
-- crossdiagonalsums (x:xs) =
--   zipWith (+) (x ++ replicate (length xs) 0) (0:crossdiagonalsums xs)
-- crossdiagonalsums [] = repeat 0

crossdiagonalsums :: Num a => [[a]] -> [a]
crossdiagonalsums (x:y:xs) =
  head x : crossdiagonalsums (zipWith (+) (tail x ++ replicate (length xs + 1) 0) y : xs)
crossdiagonalsums [x:xs] = x:xs

mult :: (Num a) => Poly a -> Poly a -> Poly a
mult (CL ps) (CL qs) = CL $ crossdiagonalsums [ [ p * q | !p <- ps ] | !q <- qs ]
-- mult (CL ((!p):ps)) (CL ((!q):qs)) = CL ((p*q) : psqs) where psqs = getCL $ CL ((p *) <$> qs) + CL ps * CL (q:qs)
-- mult _ _ = CL []

eval :: (Num a) => a -> Poly a -> a
eval x (CL p) = sum $ zipWith (*) p [x^n | n <- [0,1..] ]

constP :: a -> Poly a
constP v = CL [v]

diffPoly :: (Num a) => Poly a -> Poly a
diffPoly (CL ps) = CL (zipWith (*) (tail ps) (fromIntegral <$> [1..]))

x :: Num a => Poly a
x = CL [0,1]

-- Creates a Poly of degree n-1 from n different (arg,val) pairs
sampsToPoly :: (Num a, Fractional a) => [(a,a)] -> Poly a
sampsToPoly [] = CL []
sampsToPoly [(arg,val)] = CL [val]
sampsToPoly ((arg,val):samps) = let valP = constP val
                                    argP = constP arg
                                    newsamps = (\(a,v) -> (a, (v-val)/(a - arg))) <$> samps
                                    in valP + ( x - argP ) * sampsToPoly newsamps

-- if q = shiftpoly 3 p then q(x) = p(x+3), so if p(x) > 0 for x > 3 then q(x) > 0 for x > 0
-- shiftPoly :: (Num a) => a -> Poly a -> Poly a
-- shiftPoly y (CL p) = sum $ zipWith (.*) p [ (x + constP y)^n | n <- [0,1..] ]

shiftPoly :: (Num a) => a -> Poly a -> Poly a
shiftPoly y (CL p) = sum $ zipWith (.*) p $ iterate (* (x + constP y)) 1

-- if q = multarg 3 p then q(x) = p(3x)
multarg :: (Num a) => a -> Poly a -> Poly a
multarg y (CL p) = CL $ zipWith (*) p [ y^n | n <- [0,1..] ]
