module Main (main) where

import Control.Monad (forM_)
import Control.Monad.ST (ST, runST)
import Data.Hashable (hash)
import Data.Bits (testBit, complementBit, xor, shiftR, (.&.))
import Data.Word (Word16, Word32, Word64)
import Test.QuickCheck (Property, counterexample)
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Utils

import Data.Primitive

import qualified System.Random.SplitMix as SM

main :: IO ()
main = do
  putStrLn "evaluating word32arr"
  evaluate $ rnf word32arr
  putStrLn "evaluating word64arr"
  evaluate $ rnf word64arr

  defaultMain $ testGroup "hashes"
    [ testGroup "16bit"
      [ testProperty "id"         $ avalanche16 id           ==~ 1.0
      , testProperty "hashable"   $ avalanche16 hashable16   ==~ 1.0
      , testProperty "simple"     $ avalanche16 simple16     ==~ 0.0003663
      , testProperty "tabulation" $ avalanche16 tabulation16 ==~ 0.0060119
      ]
    , testGroup "32bit"
      [ testProperty "id"         $ avalanche32 id           ==~ 1.0
      , testProperty "murmur"     $ avalanche32 murmur32     ==~ 0.0003583
      , testProperty "triple"     $ avalanche32 triple32     ==~ 0.0000010
      , testProperty "tabulation" $ avalanche32 tabulation32 ==~ 0.0074592
      ]
    , testGroup "64bit"
      [ testProperty "id"         $ avalanche64 id           ==~ 1.0
      , testProperty "murmur"     $ avalanche64 murmur64     ==~ 0.0181569
      , testProperty "stafford"   $ avalanche64 stafford13   ==~ 0.0006514
      , testProperty "tabulation" $ avalanche64 tabulation64 ==~ 0.0076857
      ]
    ]

infix 4 ==~
(==~) :: Double -> Double -> Property
y ==~ x = counterexample msg (abs (x - y) < 1e-7) where
    msg = show y ++ " =/= " ++ show x

hashable16 :: Word16 -> Word16
hashable16 = fromIntegral . hash

simple16 :: Word16 -> Word16
simple16 x0 =
    let x1 = x0 `xor` (x0 `shiftR` 8)
        x2 = x1 * 0xd255
        x3 = x2 `xor` (x1 `shiftR` 5)
        x4 = x3 * 0xed45
        x5 = x4 `xor` (x4 `shiftR` 8)
    in x5

murmur32 :: Word32 -> Word32
murmur32 x0 =
    let x1 = x0 `xor` (x0 `shiftR` 16)
        x2 = x1 * 0x85ebca6b
        x3 = x2 `xor` (x1 `shiftR` 13)
        x4 = x3 * 0xc2b2ae35
        x5 = x4 `xor` (x4 `shiftR` 16)
    in x5



-- https://nullprogram.com/blog/2018/07/31/
--
-- @
-- uint32_t
-- triple32(uint32_t x)
-- {
--     x ^= x >> 17;
--     x *= UINT32_C(0xed5ad4bb);
--     x ^= x >> 11;
--     x *= UINT32_C(0xac4c1b51);
--     x ^= x >> 15;
--     x *= UINT32_C(0x31848bab);
--     x ^= x >> 14;
--     return x;
-- }
-- @
triple32 :: Word32 -> Word32
triple32 x0 =
    let x1 = x0 `xor` (x0 `shiftR` 17)
        x2 = x1 * 0xed5ad4bb
        x3 = x2 `xor` (x1 `shiftR` 11)
        x4 = x3 * 0xac4c1b51
        x5 = x4 `xor` (x4 `shiftR` 15)
        x6 = x5 * 0x31848bab
        x7 = x6 `xor` (x6 `shiftR` 14)
    in x7

murmur64 :: Word64 -> Word64
murmur64 x0 =
    let x1 = x0 `xor` (x0 `shiftR` 33)
        x2 = x1 * 0xff51afd7ed558ccd
        x3 = x2 `xor` (x1 `shiftR` 33)
        x4 = x3 * 0xc4ceb9fe1a85ec53
        x5 = x4 `xor` (x4 `shiftR` 33)
    in x5

-- http://zimbry.blogspot.fi/2011/09/better-bit-mixing-improving-on.html
-- Mix13
stafford13 :: Word64 -> Word64
stafford13 x0 =
    let x1 = x0 `xor` (x0 `shiftR` 30)
        x2 = x1 * 0xbf58476d1ce4e5b9
        x3 = x2 `xor` (x1 `shiftR` 27)
        x4 = x3 * 0x94d049bb133111eb
        x5 = x4 `xor` (x4 `shiftR` 31)
    in x5

-------------------------------------------------------------------------------
-- Simple tabulation
-------------------------------------------------------------------------------

tabulation16 :: Word16 -> Word16
tabulation16 w =
    aux          w    `xor`
    aux' (shiftR w 8)
  where
    aux :: Word16 -> Word16
    aux idx = indexPrimArray table16 (fromIntegral (idx .&. 0xff))
    {-# INLINE aux #-}

    aux' :: Word16 -> Word16
    aux' idx = indexPrimArray table16 (256 + fromIntegral idx)
    {-# INLINE aux' #-}

table16 :: PrimArray Word16
table16 = primArrayFromList $ map fromIntegral $ finiteList (SM.mkSMGen 0x1337) (2 * 256)

tabulation32 :: Word32 -> Word32
tabulation32 w =
    aux    0         w     `xor`
    aux  256 (shiftR w 8 ) `xor`
    aux  512 (shiftR w 16) `xor`
    aux' 768 (shiftR w 24)
  where
    aux :: Int -> Word32 -> Word32
    aux off idx = indexPrimArray table32 (off + fromIntegral (idx .&. 0xff))
    {-# INLINE aux #-}

    aux' :: Int -> Word32 -> Word32
    aux' off idx = indexPrimArray table32 (off + fromIntegral idx)
    {-# INLINE aux' #-}

table32 :: PrimArray Word32
table32 = primArrayFromList $ map fromIntegral $ finiteList (SM.mkSMGen 0x1337) (4 * 256)
{-# NOINLINE table32 #-}

tabulation64 :: Word64 -> Word64
tabulation64 w =
    aux     0         w     `xor`
    aux   256 (shiftR w 8 ) `xor`
    aux   512 (shiftR w 16) `xor`
    aux   768 (shiftR w 24) `xor`
    aux  1024 (shiftR w 32) `xor`
    aux  1280 (shiftR w 40) `xor`
    aux  1536 (shiftR w 48) `xor`
    aux' 1792 (shiftR w 56)
  where
    aux :: Int -> Word64 -> Word64
    aux off  idx = indexPrimArray table64 (off + fromIntegral (idx .&. 0xff))
    {-# INLINE aux #-}

    aux' :: Int -> Word64 -> Word64
    aux' off  idx = indexPrimArray table64 (off + fromIntegral idx)
    {-# INLINE aux' #-}

table64 :: PrimArray Word64
table64 = primArrayFromList $ finiteList (SM.mkSMGen 0x1337) (8 * 256)
{-# NOINLINE table64 #-}

-------------------------------------------------------------------------------
-- Utils
-------------------------------------------------------------------------------

sq :: Num a => a ->  a
sq x = x * x

-------------------------------------------------------------------------------
-- Avalanche 16bit
-------------------------------------------------------------------------------

avalanche16 :: (Word16 -> Word16) -> Double
avalanche16 f = do
    foldlPrimArray' aux 0 arr / fromIntegral (sq bits)
  where
    bits  = 16 :: Int
    size  = 65536 :: Int
    hsize' = fromIntegral size / 2 :: Double

    aux :: Double -> Word32 -> Double
    aux acc n = acc + sq ((n' - hsize') / hsize')
      where
        n' = fromIntegral n

    arr = runST $ do
        acc <- newPrimArray (sq bits)
        forM_ [ 0 .. sq bits - 1] $ \idx -> writePrimArray acc idx 0

        -- calculate all numbers
        forM_ [ minBound .. maxBound ] $ \u -> do
            avalancheStep16 u f acc

        unsafeFreezePrimArray acc

avalancheStep16
    :: Word16
    -> (Word16 -> Word16)
    -> MutablePrimArray s Word32
    -> ST s ()
avalancheStep16 u f acc = do
    forM_ [0 .. 15 :: Int] $ \i -> do
        -- with a single bit flipped
        let v = complementBit u i

        -- apply function
        let hu = f u
            hv = f v
            ne = hu `xor` hv

        -- for each output bit
        forM_ [0 .. 15 :: Int] $ \j -> do
            let idx = i * 16 + j
            n <- readPrimArray acc idx
            writePrimArray acc idx $ n + if testBit ne j then 1 else 0

-------------------------------------------------------------------------------
-- Avalanche 32bit
-------------------------------------------------------------------------------

avalanche32 :: (Word32 -> Word32) -> Double
avalanche32 f = do
    foldlPrimArray' aux 0 arr / fromIntegral (sq bits)
  where
    bits  = 32 :: Int
    size  = size32
    hsize' = fromIntegral size / 2 :: Double

    aux :: Double -> Word64 -> Double
    aux acc n = acc + sq ((n' - hsize') / hsize')
      where
        n' = fromIntegral n

    arr = runST $ do
        acc <- newPrimArray (sq bits)
        forM_ [ 0 .. sq bits - 1] $ \idx -> writePrimArray acc idx 0

        -- calculate all numbers
        flip traversePrimArray_ word32arr $ \u -> do
            avalancheStep32 u f acc

        unsafeFreezePrimArray acc

size32 :: Int
size32 = 2 ^ (20 :: Int)

word32arr :: PrimArray Word32
word32arr = primArrayFromList $ take size32 $ hashNub $ go (SM.mkSMGen 0xbeef) where
    go g = let (w,g') = SM.nextWord64 g in fromIntegral w : go g'

avalancheStep32
    :: Word32
    -> (Word32 -> Word32)
    -> MutablePrimArray s Word64
    -> ST s ()
avalancheStep32 u f acc = do
    forM_ [0 .. 31 :: Int] $ \i -> do
        -- with a single bit flipped
        let v = complementBit u i

        -- apply function
        let hu = f u
            hv = f v
            ne = hu `xor` hv

        -- for each output bit
        forM_ [0 .. 31 :: Int] $ \j -> do
            let idx = i * 32 + j
            n <- readPrimArray acc idx
            writePrimArray acc idx $ n + if testBit ne j then 1 else 0

-------------------------------------------------------------------------------
-- Avalanche 64bit
-------------------------------------------------------------------------------

avalanche64 :: (Word64 -> Word64) -> Double
avalanche64 f = do
    foldlPrimArray' aux 0 arr / fromIntegral (sq bits)
  where
    bits  = 64 :: Int
    size  = size64
    hsize' = fromIntegral size / 2 :: Double

    aux :: Double -> Word64 -> Double
    aux acc n = acc + sq ((n' - hsize') / hsize')
      where
        n' = fromIntegral n

    arr = runST $ do
        acc <- newPrimArray (sq bits)
        forM_ [ 0 .. sq bits - 1] $ \idx -> writePrimArray acc idx 0

        -- calculate all numbers
        flip traversePrimArray_ word64arr $ \u -> do
            avalancheStep64 u f acc

        unsafeFreezePrimArray acc

size64 :: Int
size64 = 2 ^ (20 :: Int)

word64arr :: PrimArray Word64
word64arr = primArrayFromList $ take size64 $ hashNub $ go (SM.mkSMGen 0xbeef) where
    go g = let (w,g') = SM.nextWord64 g in fromIntegral w : go g'

avalancheStep64
    :: Word64
    -> (Word64 -> Word64)
    -> MutablePrimArray s Word64
    -> ST s ()
avalancheStep64 u f acc = do
    forM_ [0 .. 63 :: Int] $ \i -> do
        -- with a single bit flipped
        let v = complementBit u i

        -- apply function
        let hu = f u
            hv = f v
            ne = hu `xor` hv

        -- for each output bit
        forM_ [0 .. 63 :: Int] $ \j -> do
            let idx = i * 64 + j
            n <- readPrimArray acc idx
            writePrimArray acc idx $ n + if testBit ne j then 1 else 0
