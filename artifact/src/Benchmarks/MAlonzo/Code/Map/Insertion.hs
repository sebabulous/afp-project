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

module MAlonzo.Code.Map.Insertion where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Map.Map
import qualified MAlonzo.Code.Map.QQuery

-- Map.Insertion.insert
d_insert_8 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
d_insert_8 ~v0 ~v1 v2 v3 v4 v5 = du_insert_8 v2 v3 v4 v5
du_insert_8 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
du_insert_8 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Map.Map.C_tip_182
        -> coe
             MAlonzo.Code.Map.Map.C_node_184 (coe (1 :: Integer)) (coe v1)
             (coe v2) (coe v3) (coe v3)
      MAlonzo.Code.Map.Map.C_node_184 v4 v5 v6 v7 v8
        -> let v9 = coe MAlonzo.Code.Map.Map.d_compare_54 v0 v1 v5 in
           coe
             (case coe v9 of
                MAlonzo.Code.Map.Map.C_eq_16
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184 (coe v4) (coe v1) (coe v2) (coe v7)
                       (coe v8)
                MAlonzo.Code.Map.Map.C_lt_18
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe du_insert_8 (coe v0) (coe v1) (coe v2) (coe v7))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v8)))
                       (coe v5) (coe v6)
                       (coe du_insert_8 (coe v0) (coe v1) (coe v2) (coe v7)) (coe v8)
                MAlonzo.Code.Map.Map.C_gt_20
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe du_insert_8 (coe v0) (coe v1) (coe v2) (coe v8))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v7)))
                       (coe v5) (coe v6) (coe v7)
                       (coe du_insert_8 (coe v0) (coe v1) (coe v2) (coe v8))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Insertion.insertWith
d_insertWith_78 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
d_insertWith_78 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_insertWith_78 v2 v3 v4 v5 v6
du_insertWith_78 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
du_insertWith_78 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_182
        -> coe
             MAlonzo.Code.Map.Map.C_node_184 (coe (1 :: Integer)) (coe v2)
             (coe v3) (coe v4) (coe v4)
      MAlonzo.Code.Map.Map.C_node_184 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_54 v0 v2 v6 in
           coe
             (case coe v10 of
                MAlonzo.Code.Map.Map.C_eq_16
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184 (coe v5) (coe v2) (coe v1 v3 v7)
                       (coe v8) (coe v9)
                MAlonzo.Code.Map.Map.C_lt_18
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe
                                   du_insertWith_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v9)))
                       (coe v6) (coe v7)
                       (coe du_insertWith_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8))
                       (coe v9)
                MAlonzo.Code.Map.Map.C_gt_20
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe
                                   du_insertWith_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v8)))
                       (coe v6) (coe v7) (coe v8)
                       (coe du_insertWith_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Insertion.insertWithKey
d_insertWithKey_158 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
d_insertWithKey_158 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_insertWithKey_158 v2 v3 v4 v5 v6
du_insertWithKey_158 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_176 -> MAlonzo.Code.Map.Map.T_Map_176
du_insertWithKey_158 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_182
        -> coe
             MAlonzo.Code.Map.Map.C_node_184 (coe (1 :: Integer)) (coe v2)
             (coe v3) (coe v4) (coe v4)
      MAlonzo.Code.Map.Map.C_node_184 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_54 v0 v2 v6 in
           coe
             (case coe v10 of
                MAlonzo.Code.Map.Map.C_eq_16
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184 (coe v5) (coe v2) (coe v1 v2 v3 v7)
                       (coe v8) (coe v9)
                MAlonzo.Code.Map.Map.C_lt_18
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe
                                   du_insertWithKey_158 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v8))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v9)))
                       (coe v6) (coe v7)
                       (coe
                          du_insertWithKey_158 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8))
                       (coe v9)
                MAlonzo.Code.Map.Map.C_gt_20
                  -> coe
                       MAlonzo.Code.Map.Map.C_node_184
                       (coe
                          addInt
                          (coe
                             addInt (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Map.QQuery.d_size_14
                                (coe
                                   du_insertWithKey_158 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v9))))
                          (coe MAlonzo.Code.Map.QQuery.d_size_14 (coe v8)))
                       (coe v6) (coe v7) (coe v8)
                       (coe
                          du_insertWithKey_158 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
