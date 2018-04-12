{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module SimplePoly_NFData
  ( Poly(CL)
  , getCL
  , constP
  , padtodeg
  , deg
  , eval
  , shiftPoly
  , sampsToPoly
  , diffPoly
  ) where

import GHC.Generics (Generic)
import Control.DeepSeq

newtype Poly a = CL { getCL :: [a] } deriving (Show, Generic, NFData)

deg :: Poly a -> Int
deg (CL p) = length p - 1

padtodeg :: (Num a) => Int -> Poly a -> Poly a
padtodeg n (CL p) = CL (p ++ take (n - length p + 1) (fromInteger <$> [0,0..]))

instance (Num a, NFData a) => Num (Poly a) where
  (+) = add
  (*) = mult
  fromInteger a = CL [fromInteger a]
  negate (CL p) = CL (map negate p)
  signum = undefined
  abs = undefined

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

add :: (NFData a, Num a) => Poly a -> Poly a -> Poly a
add (CL (p:ps)) (CL (q:qs)) = CL (p + q : psqs) where psqs = getCL $ CL ps + CL qs
add p (CL []) = p
add (CL []) p = p

mult :: (NFData a, Num a) => Poly a -> Poly a -> Poly a
mult (CL (p:ps)) (CL (q:qs)) = CL ((p*q) : psqs) where psqs = getCL $ CL [p] * CL qs + CL ps * CL (q:qs)
mult _ _ = CL []

eval :: (NFData a, Num a) => a -> Poly a -> a
eval x (CL p) = sum $ zipWith (*) p [x^n | n <- [0,1..] ]

constP :: a -> Poly a
constP v = CL [v]

diffPoly :: (NFData a, Num a) => Poly a -> Poly a
diffPoly (CL ps) = CL (zipWith (*) (tail ps) (fromIntegral <$> [1..]))

x :: Num a => Poly a
x = CL [0,1]

-- Creates a Poly of degree n-1 from n different (arg,val) pairs
sampsToPoly :: (NFData a, Num a, Fractional a) => [(a,a)] -> Poly a
sampsToPoly [] = CL []
sampsToPoly [(arg,val)] = CL [val]
sampsToPoly ((arg,val):samps) = let valP = constP val
                                    argP = constP arg
                                    newsamps = (\(a,v) -> (a, (v-val)/(a - arg))) <$> samps
                                    in valP + ( x - argP ) * sampsToPoly newsamps

-- if q = shiftpoly 3 p then q(x) = p(x+3), so if p(x) > 0 for x > 3 then q(x) > 0 for x > 0
shiftPoly :: (NFData a, Num a) => a -> Poly a -> Poly a
shiftPoly y (CL p) = sum $ zipWith (\c m -> constP c * m) p [ (x + constP y)^n | n <- [0,1..] ]
