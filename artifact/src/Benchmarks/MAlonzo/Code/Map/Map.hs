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

module MAlonzo.Code.Map.Map where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool

-- Map.Map._||_
d__'124''124'__4 :: Bool -> Bool -> Bool
d__'124''124'__4 v0 v1
  = let v2
          = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Bool.C_true_10 -> coe v1
                 _ -> coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10 -> coe v0
         _ -> coe v2)
-- Map.Map._&&_
d__'38''38'__6 :: Bool -> Bool -> Bool
d__'38''38'__6 v0 v1
  = let v2
          = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
            coe
              (case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Bool.C_false_8 -> coe v1
                 _ -> coe v2) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Bool.C_false_8 -> coe v0
         _ -> coe v2)
-- Map.Map.Ord
d_Ord_8 = ()
data T_Ord_8 = C_eq_10 | C_lt_12 | C_gt_14
-- Map.Map.Pair
d_Pair_20 a0 a1 = ()
data T_Pair_20 = C__'44'__34 AgdaAny AgdaAny
-- Map.Map.Pair.fst
d_fst_30 :: T_Pair_20 -> AgdaAny
d_fst_30 v0
  = case coe v0 of
      C__'44'__34 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Pair.snd
d_snd_32 :: T_Pair_20 -> AgdaAny
d_snd_32 v0
  = case coe v0 of
      C__'44'__34 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Comparable
d_Comparable_38 a0 = ()
newtype T_Comparable_38
  = C_Comparable'46'constructor_343 (AgdaAny -> AgdaAny -> T_Ord_8)
-- Map.Map.Comparable.compare
d_compare_44 :: T_Comparable_38 -> AgdaAny -> AgdaAny -> T_Ord_8
d_compare_44 v0
  = case coe v0 of
      C_Comparable'46'constructor_343 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.compare
d_compare_48 :: T_Comparable_38 -> AgdaAny -> AgdaAny -> T_Ord_8
d_compare_48 v0 = coe d_compare_44 (coe v0)
-- Map.Map.NatCmp
d_NatCmp_50 :: T_Comparable_38
d_NatCmp_50
  = coe
      C_Comparable'46'constructor_343
      (coe
         (\ v0 ->
            case coe v0 of
              0 -> coe
                     (\ v1 ->
                        case coe v1 of
                          0 -> coe C_eq_10
                          _ -> coe C_lt_12)
              _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
                   coe
                     (coe
                        (\ v2 ->
                           case coe v2 of
                             0 -> coe C_gt_14
                             _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                                  coe (coe d_compare_44 d_NatCmp_50 v1 v3)))))
-- Map.Map.Functor
d_Functor_60 a0 = ()
newtype T_Functor_60
  = C_Functor'46'constructor_721 (() ->
                                  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Map.Map.Functor.fmap
d_fmap_74 ::
  T_Functor_60 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_74 v0
  = case coe v0 of
      C_Functor'46'constructor_721 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.fmap
d_fmap_78 ::
  T_Functor_60 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_78 v0 = coe d_fmap_74 (coe v0)
-- Map.Map.Applicative
d_Applicative_82 a0 = ()
data T_Applicative_82
  = C_Applicative'46'constructor_957 (() -> AgdaAny -> AgdaAny)
                                     (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
                                     (() ->
                                      () ->
                                      () ->
                                      () ->
                                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
                                      AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Map.Map.Applicative.pure
d_pure_108 :: T_Applicative_82 -> () -> AgdaAny -> AgdaAny
d_pure_108 v0
  = case coe v0 of
      C_Applicative'46'constructor_957 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Applicative._<*>_
d__'60''42''62'__114 ::
  T_Applicative_82 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__114 v0
  = case coe v0 of
      C_Applicative'46'constructor_957 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Applicative.liftA3
d_liftA3_124 ::
  T_Applicative_82 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_liftA3_124 v0
  = case coe v0 of
      C_Applicative'46'constructor_957 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._._<*>_
d__'60''42''62'__128 ::
  T_Applicative_82 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__128 v0 = coe d__'60''42''62'__114 (coe v0)
-- Map.Map._.liftA3
d_liftA3_130 ::
  T_Applicative_82 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_liftA3_130 v0 = coe d_liftA3_124 (coe v0)
-- Map.Map._.pure
d_pure_132 :: T_Applicative_82 -> () -> AgdaAny -> AgdaAny
d_pure_132 v0 = coe d_pure_108 (coe v0)
-- Map.Map.Monoid
d_Monoid_136 a0 = ()
data T_Monoid_136
  = C_Monoid'46'constructor_1103 AgdaAny
                                 (AgdaAny -> AgdaAny -> AgdaAny)
-- Map.Map.Monoid.mempty
d_mempty_144 :: T_Monoid_136 -> AgdaAny
d_mempty_144 v0
  = case coe v0 of
      C_Monoid'46'constructor_1103 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Monoid.mappend
d_mappend_146 :: T_Monoid_136 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_146 v0
  = case coe v0 of
      C_Monoid'46'constructor_1103 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.mappend
d_mappend_150 :: T_Monoid_136 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_150 v0 = coe d_mappend_146 (coe v0)
-- Map.Map._.mempty
d_mempty_152 :: T_Monoid_136 -> AgdaAny
d_mempty_152 v0 = coe d_mempty_144 (coe v0)
-- Map.Map.Map
d_Map_158 a0 a1 = ()
data T_Map_158
  = C_tip_164 |
    C_node_166 Integer AgdaAny AgdaAny T_Map_158 T_Map_158
-- Map.Map.Equal
d_Equal_170 a0 = ()
newtype T_Equal_170
  = C_Equal'46'constructor_1281 (AgdaAny -> AgdaAny -> Bool)
-- Map.Map.Equal.equal
d_equal_176 :: T_Equal_170 -> AgdaAny -> AgdaAny -> Bool
d_equal_176 v0
  = case coe v0 of
      C_Equal'46'constructor_1281 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.equal
d_equal_180 :: T_Equal_170 -> AgdaAny -> AgdaAny -> Bool
d_equal_180 v0 = coe d_equal_176 (coe v0)
-- Map.Map.EqMap
d_EqMap_186 ::
  () -> () -> T_Equal_170 -> T_Equal_170 -> T_Equal_170
d_EqMap_186 ~v0 ~v1 v2 v3 = du_EqMap_186 v2 v3
du_EqMap_186 :: T_Equal_170 -> T_Equal_170 -> T_Equal_170
du_EqMap_186 v0 v1
  = coe
      C_Equal'46'constructor_1281
      (coe
         (\ v2 ->
            case coe v2 of
              C_tip_164
                -> coe
                     (\ v3 ->
                        let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (case coe v3 of
                             C_tip_164 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                             _ -> coe v4))
              C_node_166 v3 v4 v5 v6 v7
                -> coe
                     (\ v8 ->
                        let v9 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (case coe v8 of
                             C_node_166 v10 v11 v12 v13 v14
                               -> coe
                                    d__'38''38'__6
                                    (coe
                                       d__'38''38'__6
                                       (coe
                                          d__'38''38'__6
                                          (coe
                                             d__'38''38'__6 (coe eqInt (coe v3) (coe v10))
                                             (coe d_equal_176 v0 v4 v11))
                                          (coe d_equal_176 v1 v5 v12))
                                       (coe
                                          d_equal_176 (coe du_EqMap_186 (coe v0) (coe v1)) v6 v13))
                                    (coe d_equal_176 (coe du_EqMap_186 (coe v0) (coe v1)) v7 v14)
                             _ -> coe v9))
              _ -> MAlonzo.RTE.mazUnreachableError))
