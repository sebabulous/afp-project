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

module MAlonzo.Code.Map.Construction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Map.Insertion
import qualified MAlonzo.Code.Map.Map

-- Map.Construction.empty
d_empty_8 :: () -> () -> MAlonzo.Code.Map.Map.T_Map_176
d_empty_8 ~v0 ~v1 = du_empty_8
du_empty_8 :: MAlonzo.Code.Map.Map.T_Map_176
du_empty_8 = coe MAlonzo.Code.Map.Map.C_tip_182
-- Map.Construction.singleton
d_singleton_14 ::
  () -> () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_176
d_singleton_14 ~v0 ~v1 v2 v3 = du_singleton_14 v2 v3
du_singleton_14 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_176
du_singleton_14 v0 v1
  = coe
      MAlonzo.Code.Map.Map.C_node_184 (coe (1 :: Integer)) (coe v0)
      (coe v1) (coe MAlonzo.Code.Map.Map.C_tip_182)
      (coe MAlonzo.Code.Map.Map.C_tip_182)
-- Map.Construction.foldrList
d_foldrList_24 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldrList_24 ~v0 ~v1 v2 v3 v4 = du_foldrList_24 v2 v3 v4
du_foldrList_24 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldrList_24 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe v0 v3 (coe du_foldrList_24 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Construction.foldlList
d_foldlList_40 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldlList_40 ~v0 ~v1 v2 v3 v4 = du_foldlList_40 v2 v3 v4
du_foldlList_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldlList_40 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4 -> coe du_foldlList_40 (coe v0) (coe v0 v1 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Construction.fromList
d_fromList_56 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromList_56 ~v0 ~v1 v2 = du_fromList_56 v2
du_fromList_56 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromList_56 v0
  = coe
      du_foldlList_40
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insert_8 (coe v0)
              (coe MAlonzo.Code.Map.Map.d_fst_36 (coe v2))
              (coe MAlonzo.Code.Map.Map.d_snd_38 (coe v2)) (coe v1)))
      (coe MAlonzo.Code.Map.Map.C_tip_182)
-- Map.Construction.fromListWith
d_fromListWith_70 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromListWith_70 ~v0 ~v1 v2 v3 = du_fromListWith_70 v2 v3
du_fromListWith_70 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromListWith_70 v0 v1
  = coe
      du_foldlList_40
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insertWith_78 (coe v0) (coe v1)
              (coe MAlonzo.Code.Map.Map.d_fst_36 (coe v3))
              (coe MAlonzo.Code.Map.Map.d_snd_38 (coe v3)) (coe v2)))
      (coe MAlonzo.Code.Map.Map.C_tip_182)
-- Map.Construction.fromListWithKey
d_fromListWithKey_86 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromListWithKey_86 ~v0 ~v1 v2 v3 = du_fromListWithKey_86 v2 v3
du_fromListWithKey_86 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromListWithKey_86 v0 v1
  = coe
      du_foldlList_40
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insertWithKey_158 (coe v0) (coe v1)
              (coe MAlonzo.Code.Map.Map.d_fst_36 (coe v3))
              (coe MAlonzo.Code.Map.Map.d_snd_38 (coe v3)) (coe v2)))
      (coe MAlonzo.Code.Map.Map.C_tip_182)
-- Map.Construction.fromAscList
d_fromAscList_102 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromAscList_102 ~v0 ~v1 v2 = du_fromAscList_102 v2
du_fromAscList_102 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromAscList_102 v0
  = coe du_fromAscListWithKey_114 v0 (\ v1 v2 v3 -> v2)
-- Map.Construction.fromAscListWith
d_fromAscListWith_108 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromAscListWith_108 ~v0 ~v1 v2 v3 = du_fromAscListWith_108 v2 v3
du_fromAscListWith_108 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromAscListWith_108 v0 v1
  = coe du_fromAscListWithKey_114 v0 (\ v2 -> v1)
-- Map.Construction.fromAscListWithKey
d_fromAscListWithKey_114 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromAscListWithKey_114 ~v0 ~v1 v2 = du_fromAscListWithKey_114 v2
du_fromAscListWithKey_114 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromAscListWithKey_114 v0
  = coe d_unsolved'35'meta'46'85_4863 erased erased v0
-- Map.Construction.fromDistinctAscList
d_fromDistinctAscList_120 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromDistinctAscList_120 ~v0 ~v1 v2
  = du_fromDistinctAscList_120 v2
du_fromDistinctAscList_120 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromDistinctAscList_120 v0
  = coe d_unsolved'35'meta'46'86_4865 erased erased v0
-- Map.Construction.fromDescList
d_fromDescList_140 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromDescList_140 ~v0 ~v1 v2 = du_fromDescList_140 v2
du_fromDescList_140 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromDescList_140 v0
  = coe du_fromDescListWithKey_152 v0 (\ v1 v2 v3 -> v2)
-- Map.Construction.fromDescListWith
d_fromDescListWith_146 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromDescListWith_146 ~v0 ~v1 v2 v3
  = du_fromDescListWith_146 v2 v3
du_fromDescListWith_146 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromDescListWith_146 v0 v1
  = coe du_fromDescListWithKey_152 v0 (\ v2 -> v1)
-- Map.Construction.fromDescListWithKey
d_fromDescListWithKey_152 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromDescListWithKey_152 ~v0 ~v1 v2
  = du_fromDescListWithKey_152 v2
du_fromDescListWithKey_152 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromDescListWithKey_152 v0
  = coe d_unsolved'35'meta'46'116_4867 erased erased v0
-- Map.Construction.fromDistinctDescList
d_fromDistinctDescList_158 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
d_fromDistinctDescList_158 ~v0 ~v1 v2
  = du_fromDistinctDescList_158 v2
du_fromDistinctDescList_158 ::
  MAlonzo.Code.Map.Map.T_Comparable_44 ->
  [MAlonzo.Code.Map.Map.T_Pair_26] -> MAlonzo.Code.Map.Map.T_Map_176
du_fromDistinctDescList_158 v0
  = coe d_unsolved'35'meta'46'117_4869 erased erased v0
-- Map.Construction.unsolved#meta.85
d_unsolved'35'meta'46'85_4863
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.85"
-- Map.Construction.unsolved#meta.86
d_unsolved'35'meta'46'86_4865
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.86"
-- Map.Construction.unsolved#meta.116
d_unsolved'35'meta'46'116_4867
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.116"
-- Map.Construction.unsolved#meta.117
d_unsolved'35'meta'46'117_4869
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.117"
