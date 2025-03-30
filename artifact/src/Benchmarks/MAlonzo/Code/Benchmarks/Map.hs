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
import qualified MAlonzo.Code.Map.Insertion
import qualified MAlonzo.Code.Map.Map

-- Benchmarks.Map.insertMapLazy
d_insertMapLazy_4 ::
  Integer ->
  MAlonzo.Code.Map.Map.T_Map_158 -> MAlonzo.Code.Map.Map.T_Map_158
d_insertMapLazy_4 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_insertMapLazy_4 (coe v2)
                (coe
                   MAlonzo.Code.Map.Insertion.du_insert_8
                   (coe MAlonzo.Code.Map.Map.d_NatCmp_50) (coe v0) (coe v0) (coe v1)))
