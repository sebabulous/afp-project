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
d_empty_8 :: () -> () -> MAlonzo.Code.Map.Map.T_Map_158
d_empty_8 ~v0 ~v1 = du_empty_8
du_empty_8 :: MAlonzo.Code.Map.Map.T_Map_158
du_empty_8 = coe MAlonzo.Code.Map.Map.C_tip_164
-- Map.Construction.singleton
d_singleton_14 ::
  () -> () -> AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158
d_singleton_14 ~v0 ~v1 v2 v3 = du_singleton_14 v2 v3
du_singleton_14 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Map.Map.T_Map_158
du_singleton_14 v0 v1
  = coe
      MAlonzo.Code.Map.Map.C_node_166 (coe (1 :: Integer)) (coe v0)
      (coe v1) (coe MAlonzo.Code.Map.Map.C_tip_164)
      (coe MAlonzo.Code.Map.Map.C_tip_164)
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
d_foldlList_42 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldlList_42 ~v0 ~v1 v2 v3 v4 = du_foldlList_42 v2 v3 v4
du_foldlList_42 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldlList_42 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4 -> coe du_foldlList_42 (coe v0) (coe v0 v1 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Construction.fromList
d_fromList_58 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromList_58 ~v0 ~v1 v2 = du_fromList_58 v2
du_fromList_58 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromList_58 v0
  = coe
      du_foldlList_42
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insert_8 (coe v0)
              (coe MAlonzo.Code.Map.Map.d_fst_30 (coe v2))
              (coe MAlonzo.Code.Map.Map.d_snd_32 (coe v2)) (coe v1)))
      (coe MAlonzo.Code.Map.Map.C_tip_164)
-- Map.Construction.fromListWith
d_fromListWith_72 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromListWith_72 ~v0 ~v1 v2 v3 = du_fromListWith_72 v2 v3
du_fromListWith_72 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromListWith_72 v0 v1
  = coe
      du_foldlList_42
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insertWith_82 (coe v0) (coe v1)
              (coe MAlonzo.Code.Map.Map.d_fst_30 (coe v3))
              (coe MAlonzo.Code.Map.Map.d_snd_32 (coe v3)) (coe v2)))
      (coe MAlonzo.Code.Map.Map.C_tip_164)
-- Map.Construction.fromListWithKey
d_fromListWithKey_88 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromListWithKey_88 ~v0 ~v1 v2 v3 = du_fromListWithKey_88 v2 v3
du_fromListWithKey_88 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromListWithKey_88 v0 v1
  = coe
      du_foldlList_42
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Map.Insertion.du_insertWithKey_166 (coe v0) (coe v1)
              (coe MAlonzo.Code.Map.Map.d_fst_30 (coe v3))
              (coe MAlonzo.Code.Map.Map.d_snd_32 (coe v3)) (coe v2)))
      (coe MAlonzo.Code.Map.Map.C_tip_164)
-- Map.Construction.fromAscList
d_fromAscList_104 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromAscList_104 ~v0 ~v1 v2 = du_fromAscList_104 v2
du_fromAscList_104 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromAscList_104 v0
  = coe du_fromAscListWithKey_116 v0 (\ v1 v2 v3 -> v2)
-- Map.Construction.fromAscListWith
d_fromAscListWith_110 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromAscListWith_110 ~v0 ~v1 v2 v3 = du_fromAscListWith_110 v2 v3
du_fromAscListWith_110 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromAscListWith_110 v0 v1
  = coe du_fromAscListWithKey_116 v0 (\ v2 -> v1)
-- Map.Construction.fromAscListWithKey
d_fromAscListWithKey_116 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromAscListWithKey_116 ~v0 ~v1 v2 = du_fromAscListWithKey_116 v2
du_fromAscListWithKey_116 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromAscListWithKey_116 v0
  = coe d_unsolved'35'meta'46'85_4861 erased erased v0
-- Map.Construction.fromDistinctAscList
d_fromDistinctAscList_122 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromDistinctAscList_122 ~v0 ~v1 v2
  = du_fromDistinctAscList_122 v2
du_fromDistinctAscList_122 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromDistinctAscList_122 v0
  = coe d_unsolved'35'meta'46'86_4863 erased erased v0
-- Map.Construction.fromDescList
d_fromDescList_142 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromDescList_142 ~v0 ~v1 v2 = du_fromDescList_142 v2
du_fromDescList_142 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromDescList_142 v0
  = coe du_fromDescListWithKey_154 v0 (\ v1 v2 v3 -> v2)
-- Map.Construction.fromDescListWith
d_fromDescListWith_148 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromDescListWith_148 ~v0 ~v1 v2 v3
  = du_fromDescListWith_148 v2 v3
du_fromDescListWith_148 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromDescListWith_148 v0 v1
  = coe du_fromDescListWithKey_154 v0 (\ v2 -> v1)
-- Map.Construction.fromDescListWithKey
d_fromDescListWithKey_154 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromDescListWithKey_154 ~v0 ~v1 v2
  = du_fromDescListWithKey_154 v2
du_fromDescListWithKey_154 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromDescListWithKey_154 v0
  = coe d_unsolved'35'meta'46'116_4865 erased erased v0
-- Map.Construction.fromDistinctDescList
d_fromDistinctDescList_160 ::
  () ->
  () ->
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
d_fromDistinctDescList_160 ~v0 ~v1 v2
  = du_fromDistinctDescList_160 v2
du_fromDistinctDescList_160 ::
  MAlonzo.Code.Map.Map.T_Comparable_38 ->
  [MAlonzo.Code.Map.Map.T_Pair_20] -> MAlonzo.Code.Map.Map.T_Map_158
du_fromDistinctDescList_160 v0
  = coe d_unsolved'35'meta'46'117_4867 erased erased v0
-- Map.Construction.unsolved#meta.85
d_unsolved'35'meta'46'85_4861
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.85"
-- Map.Construction.unsolved#meta.86
d_unsolved'35'meta'46'86_4863
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.86"
-- Map.Construction.unsolved#meta.116
d_unsolved'35'meta'46'116_4865
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.116"
-- Map.Construction.unsolved#meta.117
d_unsolved'35'meta'46'117_4867
  = error
      "MAlonzo Runtime Error: postulate evaluated: Map.Construction.unsolved#meta.117"
