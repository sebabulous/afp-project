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
import qualified MAlonzo.Code.Agda.Builtin.Equality

-- Map.Map._||_
d__'124''124'__10 :: Bool -> Bool -> Bool
d__'124''124'__10 v0 v1
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
d__'38''38'__12 :: Bool -> Bool -> Bool
d__'38''38'__12 v0 v1
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
d_Ord_14 = ()
data T_Ord_14 = C_eq_16 | C_lt_18 | C_gt_20
-- Map.Map.Pair
d_Pair_26 a0 a1 = ()
data T_Pair_26 = C__'44'__40 AgdaAny AgdaAny
-- Map.Map.Pair.fst
d_fst_36 :: T_Pair_26 -> AgdaAny
d_fst_36 v0
  = case coe v0 of
      C__'44'__40 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Pair.snd
d_snd_38 :: T_Pair_26 -> AgdaAny
d_snd_38 v0
  = case coe v0 of
      C__'44'__40 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Comparable
d_Comparable_44 a0 = ()
newtype T_Comparable_44
  = C_Comparable'46'constructor_431 (AgdaAny -> AgdaAny -> T_Ord_14)
-- Map.Map.Comparable.compare
d_compare_54 :: T_Comparable_44 -> AgdaAny -> AgdaAny -> T_Ord_14
d_compare_54 v0
  = case coe v0 of
      C_Comparable'46'constructor_431 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Comparable.compare-reflexive
d_compare'45'reflexive_58 ::
  T_Comparable_44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compare'45'reflexive_58 = erased
-- Map.Map._.compare
d_compare_62 :: T_Comparable_44 -> AgdaAny -> AgdaAny -> T_Ord_14
d_compare_62 v0 = coe d_compare_54 (coe v0)
-- Map.Map._.compare-reflexive
d_compare'45'reflexive_64 ::
  T_Comparable_44 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compare'45'reflexive_64 = erased
-- Map.Map.NatCmp
d_NatCmp_66 :: T_Comparable_44
d_NatCmp_66
  = coe
      C_Comparable'46'constructor_431
      (\ v0 ->
         case coe v0 of
           0 -> coe
                  (\ v1 ->
                     case coe v1 of
                       0 -> coe C_eq_16
                       _ -> coe C_lt_18)
           _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
                coe
                  (coe
                     (\ v2 ->
                        case coe v2 of
                          0 -> coe C_gt_20
                          _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe (coe d_compare_54 d_NatCmp_66 v1 v3))))
-- Map.Map.Functor
d_Functor_78 a0 = ()
newtype T_Functor_78
  = C_Functor'46'constructor_917 (() ->
                                  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Map.Map.Functor.fmap
d_fmap_92 ::
  T_Functor_78 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_92 v0
  = case coe v0 of
      C_Functor'46'constructor_917 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.fmap
d_fmap_96 ::
  T_Functor_78 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_96 v0 = coe d_fmap_92 (coe v0)
-- Map.Map.Applicative
d_Applicative_100 a0 = ()
data T_Applicative_100
  = C_Applicative'46'constructor_1153 (() -> AgdaAny -> AgdaAny)
                                      (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
                                      (() ->
                                       () ->
                                       () ->
                                       () ->
                                       (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
                                       AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Map.Map.Applicative.pure
d_pure_126 :: T_Applicative_100 -> () -> AgdaAny -> AgdaAny
d_pure_126 v0
  = case coe v0 of
      C_Applicative'46'constructor_1153 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Applicative._<*>_
d__'60''42''62'__132 ::
  T_Applicative_100 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__132 v0
  = case coe v0 of
      C_Applicative'46'constructor_1153 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Applicative.liftA3
d_liftA3_142 ::
  T_Applicative_100 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_liftA3_142 v0
  = case coe v0 of
      C_Applicative'46'constructor_1153 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._._<*>_
d__'60''42''62'__146 ::
  T_Applicative_100 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__146 v0 = coe d__'60''42''62'__132 (coe v0)
-- Map.Map._.liftA3
d_liftA3_148 ::
  T_Applicative_100 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_liftA3_148 v0 = coe d_liftA3_142 (coe v0)
-- Map.Map._.pure
d_pure_150 :: T_Applicative_100 -> () -> AgdaAny -> AgdaAny
d_pure_150 v0 = coe d_pure_126 (coe v0)
-- Map.Map.Monoid
d_Monoid_154 a0 = ()
data T_Monoid_154
  = C_Monoid'46'constructor_1299 AgdaAny
                                 (AgdaAny -> AgdaAny -> AgdaAny)
-- Map.Map.Monoid.mempty
d_mempty_162 :: T_Monoid_154 -> AgdaAny
d_mempty_162 v0
  = case coe v0 of
      C_Monoid'46'constructor_1299 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map.Monoid.mappend
d_mappend_164 :: T_Monoid_154 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_164 v0
  = case coe v0 of
      C_Monoid'46'constructor_1299 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.mappend
d_mappend_168 :: T_Monoid_154 -> AgdaAny -> AgdaAny -> AgdaAny
d_mappend_168 v0 = coe d_mappend_164 (coe v0)
-- Map.Map._.mempty
d_mempty_170 :: T_Monoid_154 -> AgdaAny
d_mempty_170 v0 = coe d_mempty_162 (coe v0)
-- Map.Map.Map
d_Map_176 a0 a1 = ()
data T_Map_176
  = C_tip_182 |
    C_node_184 Integer AgdaAny AgdaAny T_Map_176 T_Map_176

instance Show T_Map_176 where
  show C_tip_182 = "tip"
  show (C_node_184 s _ _ l r) = show s ++ " k a " ++ show l ++ show r

-- Map.Map.Equal
d_Equal_188 a0 = ()
newtype T_Equal_188
  = C_Equal'46'constructor_1477 (AgdaAny -> AgdaAny -> Bool)
-- Map.Map.Equal.equal
d_equal_194 :: T_Equal_188 -> AgdaAny -> AgdaAny -> Bool
d_equal_194 v0
  = case coe v0 of
      C_Equal'46'constructor_1477 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Map.Map._.equal
d_equal_198 :: T_Equal_188 -> AgdaAny -> AgdaAny -> Bool
d_equal_198 v0 = coe d_equal_194 (coe v0)
-- Map.Map.EqMap
d_EqMap_204 ::
  () -> () -> T_Equal_188 -> T_Equal_188 -> T_Equal_188
d_EqMap_204 ~v0 ~v1 v2 v3 = du_EqMap_204 v2 v3
du_EqMap_204 :: T_Equal_188 -> T_Equal_188 -> T_Equal_188
du_EqMap_204 v0 v1
  = coe
      C_Equal'46'constructor_1477
      (coe
         (\ v2 ->
            case coe v2 of
              C_tip_182
                -> coe
                     (\ v3 ->
                        let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (case coe v3 of
                             C_tip_182 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                             _ -> coe v4))
              C_node_184 v3 v4 v5 v6 v7
                -> coe
                     (\ v8 ->
                        let v9 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                        coe
                          (case coe v8 of
                             C_node_184 v10 v11 v12 v13 v14
                               -> coe
                                    d__'38''38'__12
                                    (coe
                                       d__'38''38'__12
                                       (coe
                                          d__'38''38'__12
                                          (coe
                                             d__'38''38'__12 (coe eqInt (coe v3) (coe v10))
                                             (coe d_equal_194 v0 v4 v11))
                                          (coe d_equal_194 v1 v5 v12))
                                       (coe
                                          d_equal_194 (coe du_EqMap_204 (coe v0) (coe v1)) v6 v13))
                                    (coe d_equal_194 (coe du_EqMap_204 (coe v0) (coe v1)) v7 v14)
                             _ -> coe v9))
              _ -> MAlonzo.RTE.mazUnreachableError))
