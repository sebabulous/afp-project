{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ExistentialQuantification #-}

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

import           MAlonzo.Code.Benchmarks.Map as Agda
import           MAlonzo.Code.Map.Map as Agda.Map
import           MAlonzo.Code.Map.Construction as Agda.Construction
import           MAlonzo.Code.Map.QQuery as Agda.Query
import           MAlonzo.Code.Map.Insertion as Agda.Insertion

data InsertInt = forall f. NFData (f Integer) => InsertInt String (Integer -> f Integer)

data FromListBS = forall f. NFData (f Int) =>
      FromListBS String ([(ByteString,Int)] -> f Int)

data FromListBSAgda = forall f. NFData (f Int) =>
      FromListBSAgda String ([Agda.Map.T_Pair_20] -> f Int)

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
        [ insertInts "Haskell" (nf insertMapLazy 10) 10, 
        insertInts "Haskell" (nf insertMapLazy 100) 100, 
        insertInts "Haskell" (nf insertMapLazy 10) 1000, 
        insertInts "Haskell" (nf insertMapLazy 100) 10000,  
        insertInts "Agda" (nf Agda.d_insertMapLazy_4 10) 10, 
        insertInts "Agda" (nf Agda.d_insertMapLazy_4 100) 100,
        insertInts "Agda" (nf Agda.d_insertMapLazy_4 10) 1000, 
        insertInts "Agda" (nf Agda.d_insertMapLazy_4 100) 10000]
    , bgroup
        "Intersection (Randomized)"
        (intersection
           [ Intersection "Haskell" Data.Map.Lazy.fromList Data.Map.Lazy.intersection
            --,Intersection "Agda" Agda.Construction.d_fromList_58 Agda.Combine.intersection
            ])
    , bgroup
        "Intersection ByteString (Randomized)"
        (intersectionBS
           [ IntersectionBS "Haskell" Data.Map.Lazy.fromList Data.Map.Lazy.intersection
           --, IntersectionBS "Agda" Agda.Construction.d_fromList_58 Agda.Combine.intersection
           ])
    , bgroup
        "Lookup Int (Randomized)"
        (lookupRandomized
           [ Lookup "Haskell" Data.Map.Lazy.fromList Data.Map.Lazy.lookup
           -- , Lookup "Agda" Agda.Construction.d_fromList_58 Agda.Query.d_lookup_22
           ])
    , bgroup
        "FromList ByteString (Monotonic)" 
        (insertBSMonotonic
           [ FromListBS "Haskell" Data.Map.Lazy.fromList
           -- , FromListBS "Agda" (\x -> Agda.Construction.du_fromList_58 d_NatCmp_50 (toPair x))
           ])
    , bgroup
        "FromList ByteString (Randomized)"
        (insertBSRandomized
           [ FromListBS "Haskell" Data.Map.Lazy.fromList
           -- , FromListBSAgda "Agda" Agda.Construction.du_fromList_58 
           ])
    , bgroup
        "Lookup ByteString Monotonic"
        (lookupBSMonotonic
           [ LookupBS "Haskell" Data.Map.Lazy.fromList Data.Map.Lazy.lookup
           -- , LookupBS "Agda" Agda.Construction.du_fromList_58 Agda.Query.d_lookup_22
           ])
    , bgroup
        "Lookup ByteString Randomized"
        (lookupBSRandomized
           [ LookupBS "Haskell" Data.Map.Lazy.fromList Data.Map.Lazy.lookup
           -- , LookupBS "Agda" Agda.Construction.du_fromList_58 Agda.Query.d_lookup_22
           ])
    ]
  where
    insertInts title output i = env (pure (force (zip (randoms (mkStdGen 0) :: [Int]) [1 :: Int .. i]))) (\_ -> bench (title ++ ":" ++ show i) output)
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

insertMapLazy :: Integer -> Data.Map.Lazy.Map Integer Integer
insertMapLazy n0 = go n0 mempty
  where
    go 0 acc = acc
    go n acc = go (n - 1) (Data.Map.Lazy.insert n n acc)