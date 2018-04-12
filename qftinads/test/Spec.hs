import Blocks

blockapprox :: a -> a -> a -> RhoOrder -> Integer -> a
blockapprox a b h n m = eval h (numeratorpolys a b n !! m) / denominator h n

difference :: a -> a -> a -> RhoOrder -> a
difference a b h n = blockval a b h (1/2) - blockapprox a b h n 0

-- Casimir equations
casimirs :: (Floating a) => a -> a -> a -> Int -> [a]
casimirs a b h n = [ 4*(a*b + 2*(h-1)*h)*f + 2*(1+a+b)*f' - f''
                   , 8*a*b*f + 8*f' + 4*(a*b + 2*a + 2*b + 2*h*(h-1))*f' + 2*(a+b)*f'' - f'''
                   , 16*(1+a)*(1+b)*f'
                      + 4*(4*a + 4*b + a*b + 6 + 2*h*(h-1))*f''
                      + 2*(a+b-1)*f''' - f''''
                   ]
                   where f = blockapprox a b h n 0
                         f' = blockapprox a b h n 1
                         f'' = blockapprox a b h n 2
                         f''' = blockapprox a b h n 3
                         f'''' = blockapprox a b h n 4

main :: IO ()
main = putStrLn "Test suite not yet implemented"
