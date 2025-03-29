{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ExistentialQuantification #-}

-- This code is based on https://github.com/haskell-perf/dictionaries/tree/master 
-- The benchmarks of the other dictionary data structures are removed
module Main (main) where

import           Common ()
import           Control.Arrow
import           Control.DeepSeq
import           Control.Monad
import           Criterion.Main
import           Criterion.Types
import           Data.ByteString          (ByteString)
import qualified Data.ByteString.Char8    as S8
import           Data.List (foldl')
import qualified Data.Map.Lazy
import           System.Directory
import           System.Random

data InsertInt = forall f. NFData (f Int) => InsertInt String (Int -> f Int)

data FromListBS =
  forall f. NFData (f Int) =>
            FromListBS String
                     ([(ByteString,Int)] -> f Int)

data Intersection = forall f. NFData (f Int) =>
     Intersection String ([(Int,Int)] -> f Int) (f Int -> f Int -> f Int)

data LookupBS =
  forall f. (NFData (f Int)) =>
            LookupBS String
                     ([(ByteString, Int)] -> f Int)
                     (ByteString -> f Int -> (Maybe Int))

data IntersectionBS = forall f. NFData (f Int) =>
     IntersectionBS String ([(ByteString,Int)] -> f Int) (f Int -> f Int -> f Int)

data Lookup =
  forall f. (NFData (f Int)) =>
            Lookup String
                   ([(Int, Int)] -> f Int)
                   (Int -> f Int ->  (Maybe Int))

main :: IO ()
main = do
  let fp = "out.csv"
  exists <- doesFileExist fp
  when exists (removeFile fp)
  defaultMainWith
    defaultConfig {csvFile = Just fp}
    [ bgroup
        "Insert Int (Randomized)"
        (insertInts [ InsertInt "Data.Map.Lazy" insertMapLazy])
    , bgroup
        "Intersection (Randomized)"
        (intersection
           [ Intersection
               "Data.Map.Lazy"
               Data.Map.Lazy.fromList
               Data.Map.Lazy.intersection])
    , bgroup
        "Intersection ByteString (Randomized)"
        (intersectionBS
           [ IntersectionBS
               "Data.Map.Lazy"
               Data.Map.Lazy.fromList
               Data.Map.Lazy.intersection])
    , bgroup
        "Lookup Int (Randomized)"
        (lookupRandomized
           [ Lookup "Data.Map.Lazy" Data.Map.Lazy.fromList Data.Map.Lazy.lookup ])
    , bgroup
        "FromList ByteString (Monotonic)"
        (insertBSMonotonic
           [ FromListBS "Data.Map.Lazy" Data.Map.Lazy.fromList])
    , bgroup
        "FromList ByteString (Randomized)"
        (insertBSRandomized
           [ FromListBS "Data.Map.Lazy" Data.Map.Lazy.fromList])
    , bgroup
        "Lookup ByteString Monotonic"
        (lookupBSMonotonic
           [ LookupBS
               "Data.Map.Lazy"
               Data.Map.Lazy.fromList
               Data.Map.Lazy.lookup])
    , bgroup
        "Lookup ByteString Randomized"
        (lookupBSRandomized
           [ LookupBS
               "Data.Map.Lazy"
               Data.Map.Lazy.fromList
               Data.Map.Lazy.lookup])
    ]
  where
    insertInts funcs =
      [ env
        (let !elems =
               force (zip (randoms (mkStdGen 0) :: [Int]) [1 :: Int .. i])
          in pure elems)
        (\_ -> bench (title ++ ":" ++ show i) $ nf func i)
      | i <- [10, 100, 1000, 10000]
      , InsertInt title func <- funcs
      ]
    intersection funcs =
      [ env
        (let !args =
               force
                 ( build (zip (randoms (mkStdGen 0) :: [Int]) [1 :: Int .. i])
                 , build (zip (randoms (mkStdGen 1) :: [Int]) [1 :: Int .. i]))
          in pure args)
        (\args -> bench (title ++ ":" ++ show i) $ nf (uncurry intersect) args)
      | i <- [10, 100, 1000, 10000, 100000, 1000000]
      , Intersection title build intersect <- funcs
      ]
    intersectionBS funcs =
      [ env
        (let !args =
               force
                 -- ( build (zip (map (S8.pack.show) $ (randoms (mkStdGen 0) :: [Int])) [1 :: Int .. i])
                 -- , build (zip (map (S8.pack.show) $ (randoms (mkStdGen 1) :: [Int])) [1 :: Int .. i]))
                 ( build (map
                          (first (S8.pack . show))
                          (take i (zip (randoms (mkStdGen 0) :: [Int]) [1 ..])))
                 , build (map
                          (first (S8.pack . show))
                          (take i (zip (randoms (mkStdGen 1) :: [Int]) [1 ..]))))
         in pure args)
        (\args -> bench (title ++ ":" ++ show i) $ nf (uncurry intersect) args)
      | i <- [10, 100, 1000, 10000, 100000, 1000000]
      , IntersectionBS title build intersect <- funcs
      ]
    insertBSRandomized funcs =
      [ env
        (let !elems =
               force
                 (map
                    (first (S8.pack . show))
                    (take i (zip (randoms (mkStdGen 0) :: [Int]) [1 ..])))
          in pure elems)
        (\elems -> bench (title ++ ":" ++ show i) $ nf func elems)
      | i <- [10, 100, 1000, 10000]
      , FromListBS title func <- funcs
      ]
    lookupRandomized funcs =
      [ env
        (let list = take i (zip (randoms (mkStdGen 0) :: [Int]) [1 ..])
             !elems = force (fromList list)
          in pure (list, elems))
        (\(~(list, elems)) ->
           bench (title ++ ":" ++ show i) $
           nf
             (\ks ->
                foldl'
                  (\_ k ->
                     case func k elems of
                       Just !v -> v
                       Nothing -> 0)
                  0
                  ks)
             (map fst list))
      | i <- [10, 100, 1000, 10000, 100000, 1000000]
      , Lookup title fromList func <- funcs
      ]
    lookupBSMonotonic funcs =
      [ env
        (let !list =
               force
                 (map
                    (first (S8.pack . show))
                    (take i (zip [1 :: Int ..] [1 ..])))
             (!key, _) = list !! (div i 2)
             !elems = force (fromList list)
          in pure (elems, key))
        (\(~(elems, key)) ->
           bench (title ++ ":" ++ show i) $ nf (flip func elems) key)
      | i <- [10000]
      , LookupBS title fromList func <- funcs
      ]
    lookupBSRandomized funcs =
      [ env
        (let !list =
               force
                 (map
                    (first (S8.pack . show))
                    (take i (zip (randoms (mkStdGen 0) :: [Int]) [1 ..])))
             !elems = force (fromList list)
          in pure (list, elems))
        (\(~(list, elems)) ->
           bench (title ++ ":" ++ show i) $
           nf
             (\ks ->
                foldl'
                  (\_ k ->
                     case func k elems of
                       Just !v -> v
                       Nothing -> 0)
                  0
                  ks)
             (map fst list))
      | i <- [10000]
      , LookupBS title fromList func <- funcs
      ]
    insertBSMonotonic funcs =
      [ env
        (let !elems =
               force
                 (map
                    (first (S8.pack . show))
                    (take i (zip [1 :: Int ..] [1 ..])))
          in pure elems)
        (\elems -> bench (title ++ ":" ++ show i) $ nf func elems)
      | i <- [10000]
      , FromListBS title func <- funcs
      ]

--------------------------------------------------------------------------------
-- Insert Int

insertMapLazy :: Int -> Data.Map.Lazy.Map Int Int
insertMapLazy n0 = go n0 mempty
  where
    go 0 acc = acc
    go n !acc = go (n - 1) (Data.Map.Lazy.insert n n acc)