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

module MAlonzo.Code.Map.QQuery where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Map.Map

-- Map.Query.null
d_null_8 :: () -> () -> MAlonzo.Code.Map.Map.T_Map_158 -> Bool
d_null_8 ~v0 ~v1 v2 = du_null_8 v2
du_null_8 :: MAlonzo.Code.Map.Map.T_Map_158 -> Bool
du_null_8 v0
  = case coe v0 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Map.Map.C_node_166 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.size
d_size_14 :: MAlonzo.Code.Map.Map.T_Map_158 -> Integer
d_size_14 v0
  = case coe v0 of
      MAlonzo.Code.Map.Map.C_tip_164 -> coe (0 :: Integer)
      MAlonzo.Code.Map.Map.C_node_166 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.lookup
d_lookup_22 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Maybe AgdaAny
d_lookup_22 ~v0 ~v1 v2 v3 v4 = du_lookup_22 v2 v3 v4
du_lookup_22 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Maybe AgdaAny
du_lookup_22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5)
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_lookup_22 (coe v0) (coe v1) (coe v6)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_lookup_22 (coe v0) (coe v1) (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query._!?_
d__'33''63'__82 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny -> Maybe AgdaAny
d__'33''63'__82 ~v0 ~v1 v2 v3 v4 = du__'33''63'__82 v2 v3 v4
du__'33''63'__82 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny -> Maybe AgdaAny
du__'33''63'__82 v0 v1 v2
  = coe du_lookup_22 (coe v0) (coe v2) (coe v1)
-- Map.Query._!_
d__'33'__92 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny -> AgdaAny
d__'33'__92 ~v0 ~v1 v2 v3 v4 = du__'33'__92 v2 v3 v4
du__'33'__92 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny -> AgdaAny
du__'33'__92 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe d_unsolved'35'meta'46'29_55255 erased erased v0 v2
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v2 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10 -> coe v5
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du__'33'__92 (coe v0) (coe v6) (coe v2)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du__'33'__92 (coe v0) (coe v7) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.findWithDefault
d_findWithDefault_152 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny
d_findWithDefault_152 ~v0 ~v1 v2 v3 v4 v5
  = du_findWithDefault_152 v2 v3 v4 v5
du_findWithDefault_152 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> AgdaAny
du_findWithDefault_152 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Map.Map.C_tip_164 -> coe v1
      MAlonzo.Code.Map.Map.C_node_166 v4 v5 v6 v7 v8
        -> let v9 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v2 v5 in
           coe
             (case coe v9 of
                MAlonzo.Code.Map.Map.C_eq_10 -> coe v6
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_findWithDefault_152 (coe v0) (coe v1) (coe v2) (coe v7)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_findWithDefault_152 (coe v0) (coe v1) (coe v2) (coe v8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.member
d_member_222 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Bool
d_member_222 ~v0 ~v1 v2 v3 v4 = du_member_222 v2 v3 v4
du_member_222 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Bool
du_member_222 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_member_222 (coe v0) (coe v1) (coe v6)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_member_222 (coe v0) (coe v1) (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.notMember
d_notMember_282 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Bool
d_notMember_282 ~v0 ~v1 v2 v3 v4 = du_notMember_282 v2 v3 v4
du_notMember_282 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158 -> Bool
du_notMember_282 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_notMember_282 (coe v0) (coe v1) (coe v6)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_notMember_282 (coe v0) (coe v1) (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.lookupLT
d_lookupLT_342 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_lookupLT_342 ~v0 ~v1 v2 v3 v4 = du_lookupLT_342 v2 v3 v4
du_lookupLT_342 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_lookupLT_342 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (let v9 = coe du_lookupLT_342 (coe v0) (coe v1) (coe v6) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Map.Map.C_gt_14
                     -> coe du_goJust_382 (coe v0) (coe v1) (coe v4) (coe v5) (coe v7)
                   _ -> coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query._.goJust
d_goJust_382 ::
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_goJust_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
             v13 v14 v15
  = du_goJust_382 v11 v12 v13 v14 v15
du_goJust_382 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_goJust_382 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v2) (coe v3))
      MAlonzo.Code.Map.Map.C_node_166 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v2 in
           coe
             (let v11
                    = coe du_goJust_382 (coe v0) (coe v1) (coe v6) (coe v7) (coe v8) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Map.Map.C_gt_14
                     -> coe du_goJust_382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                   _ -> coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.lookupGT
d_lookupGT_458 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_lookupGT_458 ~v0 ~v1 v2 v3 v4 = du_lookupGT_458 v2 v3 v4
du_lookupGT_458 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_lookupGT_458 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (let v9 = coe du_lookupGT_458 (coe v0) (coe v1) (coe v7) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Map.Map.C_lt_12
                     -> coe du_goJust_498 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)
                   _ -> coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query._.goJust
d_goJust_498 ::
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_goJust_498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
             v13 v14 v15
  = du_goJust_498 v11 v12 v13 v14 v15
du_goJust_498 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_goJust_498 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v2) (coe v3))
      MAlonzo.Code.Map.Map.C_node_166 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v2 in
           coe
             (let v11
                    = coe du_goJust_498 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Map.Map.C_lt_12
                     -> coe du_goJust_498 (coe v0) (coe v1) (coe v6) (coe v7) (coe v8)
                   _ -> coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.lookupLE
d_lookupLE_574 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_lookupLE_574 ~v0 ~v1 v2 = du_lookupLE_574 v2
du_lookupLE_574 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_lookupLE_574 v0 = coe du_goNothing_584 (coe v0)
-- Map.Query._.goNothing
d_goNothing_584 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_goNothing_584 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_goNothing_584 v5 v6 v7
du_goNothing_584 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_goNothing_584 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v4) (coe v5))
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_goNothing_584 (coe v0) (coe v1) (coe v6)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_goJust_638 (coe v0) (coe v1) (coe v4) (coe v5) (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query._._.goJust
d_goJust_638 ::
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_goJust_638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 v14 v15 v16 v17 v18
  = du_goJust_638 v14 v15 v16 v17 v18
du_goJust_638 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_goJust_638 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v2) (coe v3))
      MAlonzo.Code.Map.Map.C_node_166 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v6 in
           coe
             (case coe v10 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v6) (coe v7))
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_goJust_638 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_goJust_638 (coe v0) (coe v1) (coe v6) (coe v7) (coe v9)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.lookupGE
d_lookupGE_708 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_lookupGE_708 ~v0 ~v1 v2 v3 v4 = du_lookupGE_708 v2 v3 v4
du_lookupGE_708 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_lookupGE_708 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Map.Map.C_node_166 v3 v4 v5 v6 v7
        -> let v8 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v4) (coe v5))
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_goJust_760 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_lookupGE_708 (coe v0) (coe v1) (coe v7)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query._.goJust
d_goJust_760 ::
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
d_goJust_760 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
             v13 v14 v15
  = du_goJust_760 v11 v12 v13 v14 v15
du_goJust_760 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Map.Map.T_Map_158 ->
  Maybe MAlonzo.Code.Map.Map.T_Pair_20
du_goJust_760 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Map.Map.C_tip_164
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v2) (coe v3))
      MAlonzo.Code.Map.Map.C_node_166 v5 v6 v7 v8 v9
        -> let v10 = coe MAlonzo.Code.Map.Map.d_compare_44 v0 v1 v2 in
           coe
             (case coe v10 of
                MAlonzo.Code.Map.Map.C_eq_10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Map.Map.C__'44'__34 (coe v6) (coe v7))
                MAlonzo.Code.Map.Map.C_lt_12
                  -> coe du_goJust_760 (coe v0) (coe v1) (coe v6) (coe v7) (coe v8)
                MAlonzo.Code.Map.Map.C_gt_14
                  -> coe du_goJust_760 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Query.unsolved#meta.29
d_unsolved'35'meta'46'29_55255
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Query.unsolved#meta.29"
