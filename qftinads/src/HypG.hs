{-# LANGUAGE Strict #-}

module HypG
    ( hypgtermlist
    , hypgval
    ) where

import Data.List
import Data.Maybe

nestmap :: (a -> b -> b) -> b -> [a] -> [b]
nestmap _ _ [] = []
nestmap f y (x:xs) = let z = f x y in z `seq` z : nestmap f z xs

hypgterm :: (Fractional a) => Integer -> a -> a -> a -> a -> a
hypgterm n a b c z = let m = fromIntegral n in z * (a + m) * (b + m) / (c + m) / (m + 1)

hypgtermlist :: (Fractional a) => a -> a -> a -> a -> [a]
hypgtermlist a b c z = 1 : nestmap (\ m w -> w * hypgterm m a b c z) 1 [0..]

hypgpartsums :: (Fractional a) => a -> a -> a -> a -> [a]
hypgpartsums a b c z = nestmap (+) 0 (hypgtermlist a b c z)

hypgval :: (Eq a, Floating a) => a -> a -> a -> a -> a
hypgval a b c z = fst $ fromJust $ find (uncurry (==)) $ (zip <*> tail . tail) (hypgpartsums a b c z)


-- (2 h (-2 + n) + (-3 + n) (-2 + n)) c[-3 +
--     n] + (2 h (-1 + n) + (-2 + n) (-1 + n)) c[-2 +
--     n] + (h (2 - 2 n) + (2 - n) (-1 + n)) c[-1 + n]
-- blocktermlist :: (Fractional a) => a -> a -> a -> a -> [a]
-- blocktermlist h a b z = 1 :

-- hypgsum :: (Floating a) => Int -> a -> a -> a -> a -> a
-- hypgsum n a b c z = sum (take n $ hypglist a b c z)

-- hypgsump :: (Floating a, Ord a) => a -> a -> a -> a -> a -> a
-- hypgsump thr a b c z = sum (takeWhile (> thr) $ hypglist a b c z)

-- blocksum :: (Floating a) => Int -> a -> a -> a
-- blocksum n h rho = rho ** h * hypgsum n (1/2) h (h + 1/2) (rho^2)
