{-# LANGUAGE BangPatterns #-}

module WriteXMLSDP ( writeXMLSDPtoFile ) where

import SimplePoly
import Control.DeepSeq
import Control.Monad.Reader

type PolyVector a = [Poly a]
type PolyVectorMatrix a = [[PolyVector a]]
type Outputter = ReaderT FilePath IO ()

writefn :: String -> Outputter
writefn s = do
  path <- ask
  liftIO $ appendFile path s

writeXML :: String -> Outputter -> Outputter
writeXML s f = do { writefn $ "<" ++ s ++ ">"
                  ; f
                  ; writefn $ "</" ++ s ++ ">\n" }

writeXMLnum :: Show a => a -> Outputter
writeXMLnum = writefn.show

writeXMLvec :: Show a => [a] -> Outputter
writeXMLvec = mapM_ $ writeXML "elt" . writeXMLnum

writeXMLpoly :: Show a => Poly a -> Outputter
writeXMLpoly p = mapM_ (writeXML "coeff" . writeXMLnum) $ getCL p

writeXMLpolyVector :: Show a => PolyVector a -> Outputter
writeXMLpolyVector = mapM_ $ writeXML "polynomial" . writeXMLpoly

writeXMLpolyVectorMatrix :: (Floating a, Show a) => PolyVectorMatrix a -> Outputter
writeXMLpolyVectorMatrix pvm =
    do { writeXML "rows" $ writeXMLnum $ length pvm
       ; writeXML "cols" $ writeXMLnum $ length $ head pvm
       ; writeXML "elements" $
            mapM_ (writeXML "polynomialVector" . writeXMLpolyVector) (concat pvm)
       ; writeXML "samplePoints" $ writeXMLvec $ laguerreSamplePts (maxDeg + 1) `withTypeOf` [x]
       ; writeXML "sampleScalings" $ writeXMLvec $ laguerreSampleScals (maxDeg + 1) `withTypeOf` [x]
       ; writeXML "bilinearBasis" $ writeXMLpolyVector $ take ((maxDeg `quot` 2) + 1) laguerrePolys `withTypeOf` [CL [x]] }
    where
      x = head $ getCL $ head $ head $ head pvm
      maxDeg = maximum $ deg <$> concat (concat pvm)

writeXMLSDP :: (Floating a, Show a) => [a] -> [PolyVectorMatrix a] -> Outputter
writeXMLSDP optvec pvms =
        writeXML "sdp" $
            do { writeXML "objective" $ writeXMLvec optvec
               ; writeXML "polynomialVectorMatrices" $
                    mapM_ (writeXML "polynomialVectorMatrix" . writeXMLpolyVectorMatrix) pvms }

writeXMLSDPtoFile :: (Floating a, Show a) => FilePath -> [a] -> [PolyVectorMatrix a] -> IO ()
writeXMLSDPtoFile fp optvec pvms =
  do
    writeFile fp ""
    runReaderT (writeXMLSDP optvec pvms) fp

withTypeOf :: a -> a -> a
withTypeOf x y = x

-- Laguerre functions bit

laguerrePolys :: (Floating a) => [Poly a]
laguerrePolys = l0 : l1 : nestmap2 laguerrerecursion l0 l1 [1..]
  where
    l0 = CL [1]
    l1 = CL [1,-1]

nestmap2 :: (a -> b -> b -> b) -> b -> b -> [a] -> [b]
nestmap2 _ _ _ [] = []
nestmap2 f x y (n:ns) = let z = f n x y in z : nestmap2 f y z ns

laguerrerecursion :: (Floating a) => Integer -> Poly a -> Poly a -> Poly a
laguerrerecursion !k !p !q = ( (2 * kk + 1 - x) * q - kk * p) * den
  where
    x = CL [0, 1]
    kk = fromIntegral k
    den = constP (1 / (fromIntegral k + 1))

laguerreSamplePts :: Floating a => Int -> [a]
laguerreSamplePts n = (\k -> pi^2 * (4 * fi k - 1)^2 / (64 * fi n)) <$> [0..(n-1)]
  where fi = fromIntegral

laguerreSampleScals :: Floating a => Int -> [a]
laguerreSampleScals n = (exp . negate) <$> laguerreSamplePts n
