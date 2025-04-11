{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Benchmarks.Map where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Map.Construction
import qualified MAlonzo.Code.Map.Insertion
import qualified MAlonzo.Code.Map.Map

-- Benchmarks.Map.insertMapLazy
d_insertMapLazy_4 ::
  Integer ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
d_insertMapLazy_4 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_insertMapLazy_4 (coe v2)
                (coe
                   MAlonzo.Code.Map.Insertion.du_insert_8
                   (coe MAlonzo.Code.Map.Map.d_NatCmp_66) (coe v0) (coe v0) (coe v1)))
-- Benchmarks.Map.fromListLazy
d_fromListLazy_12 ::
  [Integer] -> [Integer] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromListLazy_12 v0 v1
  = coe
      MAlonzo.Code.Map.Construction.du_fromList_56
      MAlonzo.Code.Map.Map.d_NatCmp_66
      (coe du_mergeLists_22 (coe v0) (coe v1))
-- Benchmarks.Map._.mergeLists
d_mergeLists_22 ::
  [Integer] ->
  [Integer] ->
  [Integer] -> [Integer] -> [MAlonzo.Code.Map.Map.T_Pair_26]
d_mergeLists_22 ~v0 ~v1 v2 v3 = du_mergeLists_22 v2 v3
du_mergeLists_22 ::
  [Integer] -> [Integer] -> [MAlonzo.Code.Map.Map.T_Pair_26]
du_mergeLists_22 v0 v1
  = case coe v0 of
      [] -> coe v0
      (:) v2 v3
        -> case coe v1 of
             [] -> coe v1
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Map.Map.C__'44'__40 (coe v2) (coe v4))
                    (coe du_mergeLists_22 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
