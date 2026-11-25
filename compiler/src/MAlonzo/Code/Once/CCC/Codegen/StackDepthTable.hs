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

module MAlonzo.Code.Once.CCC.Codegen.StackDepthTable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Codegen.StackDepth
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.CCC.Codegen.StackDepthTable.Key
d_Key_8 :: ()
d_Key_8 = erased
-- Once.CCC.Codegen.StackDepthTable.enc-name
d_enc'45'name_10 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> [Integer]
d_enc'45'name_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> coe
             MAlonzo.Code.Data.List.Base.du_concatMap_246
             (coe du_enc'45'part_18) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.enc-part
d_enc'45'part_18 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> [Integer]
d_enc'45'part_18 ~v0 v1 = du_enc'45'part_18 v1
du_enc'45'part_18 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> [Integer]
du_enc'45'part_18 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268 (coe du_cs_26 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
         (coe du_cs_26 (coe v0)))
-- Once.CCC.Codegen.StackDepthTable._._.cs
d_cs_26 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_cs_26 ~v0 v1 = du_cs_26 v1
du_cs_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_cs_26 v0
  = coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0
-- Once.CCC.Codegen.StackDepthTable.enc-label
d_enc'45'label_28 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> [Integer]
d_enc'45'label_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_mkLabelId_20 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_enc'45'name_10 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v2) (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.enc-entry
d_enc'45'entry_36 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> [Integer]
d_enc'45'entry_36 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (1 :: Integer))
             (coe d_enc'45'label_28 (coe v1))
      MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (0 :: Integer))
             (coe d_enc'45'name_10 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Cmp
d_Cmp_42 = ()
data T_Cmp_42 = C_lt_44 | C_eq_46 | C_gt_48
-- Once.CCC.Codegen.StackDepthTable.cmp
d_cmp_50 :: [Integer] -> [Integer] -> T_Cmp_42
d_cmp_50 v0 v1
  = case coe v0 of
      []
        -> case coe v1 of
             [] -> coe C_eq_46
             (:) v2 v3 -> coe C_lt_44
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v2 v3
        -> case coe v1 of
             [] -> coe C_gt_48
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe ltInt (coe v2) (coe v4)) (coe C_lt_44)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe ltInt (coe v4) (coe v2)) (coe C_gt_48)
                       (coe d_cmp_50 (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Map
d_Map_62 a0 = ()
data T_Map_62
  = C_tip_66 | C_bin_68 Integer T_Map_62 [Integer] AgdaAny T_Map_62
-- Once.CCC.Codegen.StackDepthTable._.height
d_height_76 :: T_Map_62 -> Integer
d_height_76 v0
  = case coe v0 of
      C_tip_66 -> coe (0 :: Integer)
      C_bin_68 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.node
d_node_80 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_node_80 v0 v1 v2 v3
  = coe
      C_bin_68
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8852'__208
            (coe d_height_76 (coe v0)) (coe d_height_76 (coe v3))))
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.CCC.Codegen.StackDepthTable._.rotR
d_rotR_90 ::
  () -> T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_rotR_90 ~v0 v1 v2 v3 v4 = du_rotR_90 v1 v2 v3 v4
du_rotR_90 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_rotR_90 v0 v1 v2 v3
  = case coe v0 of
      C_tip_66
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (0 :: Integer))
                   (coe d_height_76 (coe v3))))
             (coe v0) (coe v1) (coe v2) (coe v3)
      C_bin_68 v4 v5 v6 v7 v8
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe d_height_76 (coe v5))
                   (coe
                      addInt (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                         (coe d_height_76 (coe v8)) (coe d_height_76 (coe v3))))))
             (coe v5) (coe v6) (coe v7)
             (coe
                C_bin_68
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                      (coe d_height_76 (coe v8)) (coe d_height_76 (coe v3))))
                (coe v8) (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.rotL
d_rotL_112 ::
  () -> T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_rotL_112 ~v0 v1 v2 v3 v4 = du_rotL_112 v1 v2 v3 v4
du_rotL_112 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_rotL_112 v0 v1 v2 v3
  = case coe v3 of
      C_tip_66
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe d_height_76 (coe v0)) (coe (0 :: Integer))))
             (coe v0) (coe v1) (coe v2) (coe v3)
      C_bin_68 v4 v5 v6 v7 v8
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe
                      addInt (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                         (coe d_height_76 (coe v0)) (coe d_height_76 (coe v5))))
                   (coe d_height_76 (coe v8))))
             (coe
                C_bin_68
                (coe
                   addInt (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                      (coe d_height_76 (coe v0)) (coe d_height_76 (coe v5))))
                (coe v0) (coe v1) (coe v2) (coe v5))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.fixL
d_fixL_134 ::
  () -> T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_fixL_134 ~v0 v1 v2 v3 v4 = du_fixL_134 v1 v2 v3 v4
du_fixL_134 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_fixL_134 v0 v1 v2 v3
  = case coe v0 of
      C_tip_66
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (0 :: Integer))
                   (coe d_height_76 (coe v3))))
             (coe v0) (coe v1) (coe v2) (coe v3)
      C_bin_68 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe ltInt (coe d_height_76 (coe v5)) (coe d_height_76 (coe v8)))
             (coe
                du_rotR_90 (coe du_rotL_112 (coe v5) (coe v6) (coe v7) (coe v8))
                (coe v1) (coe v2) (coe v3))
             (coe du_rotR_90 (coe v0) (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.fixR
d_fixR_158 ::
  () -> T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_fixR_158 ~v0 v1 v2 v3 v4 = du_fixR_158 v1 v2 v3 v4
du_fixR_158 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_fixR_158 v0 v1 v2 v3
  = case coe v3 of
      C_tip_66
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                   (coe d_height_76 (coe v0)) (coe (0 :: Integer))))
             (coe v0) (coe v1) (coe v2) (coe v3)
      C_bin_68 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe ltInt (coe d_height_76 (coe v8)) (coe d_height_76 (coe v5)))
             (coe
                du_rotL_112 (coe v0) (coe v1) (coe v2)
                (coe du_rotR_90 (coe v5) (coe v6) (coe v7) (coe v8)))
             (coe du_rotL_112 (coe v0) (coe v1) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.balance
d_balance_182 ::
  () -> T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_balance_182 ~v0 v1 v2 v3 v4 = du_balance_182 v1 v2 v3 v4
du_balance_182 ::
  T_Map_62 -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_balance_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         ltInt (coe addInt (coe (1 :: Integer)) (coe d_height_76 (coe v3)))
         (coe d_height_76 (coe v0)))
      (coe du_fixL_134 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            ltInt (coe addInt (coe (1 :: Integer)) (coe d_height_76 (coe v0)))
            (coe d_height_76 (coe v3)))
         (coe du_fixR_158 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe
            C_bin_68
            (coe
               addInt (coe (1 :: Integer))
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe d_height_76 (coe v0)) (coe d_height_76 (coe v3))))
            (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.CCC.Codegen.StackDepthTable._.insert
d_insert_192 :: () -> [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
d_insert_192 ~v0 v1 v2 v3 = du_insert_192 v1 v2 v3
du_insert_192 :: [Integer] -> AgdaAny -> T_Map_62 -> T_Map_62
du_insert_192 v0 v1 v2
  = case coe v2 of
      C_tip_66
        -> coe
             C_bin_68
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (0 :: Integer))
                   (coe (0 :: Integer))))
             (coe v2) (coe v0) (coe v1) (coe v2)
      C_bin_68 v3 v4 v5 v6 v7
        -> coe
             du_go_216 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe v7) (coe d_cmp_50 (coe v0) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.go
d_go_216 ::
  () ->
  [Integer] ->
  AgdaAny ->
  Integer ->
  T_Map_62 ->
  [Integer] -> AgdaAny -> T_Map_62 -> T_Cmp_42 -> T_Map_62
d_go_216 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_go_216 v1 v2 v3 v4 v5 v6 v7 v8
du_go_216 ::
  [Integer] ->
  AgdaAny ->
  Integer ->
  T_Map_62 ->
  [Integer] -> AgdaAny -> T_Map_62 -> T_Cmp_42 -> T_Map_62
du_go_216 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_lt_44
        -> coe
             du_balance_182 (coe du_insert_192 (coe v0) (coe v1) (coe v3))
             (coe v4) (coe v5) (coe v6)
      C_eq_46
        -> coe C_bin_68 (coe v2) (coe v3) (coe v0) (coe v1) (coe v6)
      C_gt_48
        -> coe
             du_balance_182 (coe v3) (coe v4) (coe v5)
             (coe du_insert_192 (coe v0) (coe v1) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.lookup
d_lookup_218 :: () -> T_Map_62 -> [Integer] -> Maybe AgdaAny
d_lookup_218 ~v0 v1 v2 = du_lookup_218 v1 v2
du_lookup_218 :: T_Map_62 -> [Integer] -> Maybe AgdaAny
du_lookup_218 v0 v1
  = case coe v0 of
      C_tip_66 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_bin_68 v2 v3 v4 v5 v6
        -> coe
             du_go_236 (coe v3) (coe v5) (coe v6) (coe v1)
             (coe d_cmp_50 (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.go
d_go_236 ::
  () ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  AgdaAny -> T_Map_62 -> [Integer] -> T_Cmp_42 -> Maybe AgdaAny
d_go_236 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 = du_go_236 v2 v4 v5 v6 v7
du_go_236 ::
  T_Map_62 ->
  AgdaAny -> T_Map_62 -> [Integer] -> T_Cmp_42 -> Maybe AgdaAny
du_go_236 v0 v1 v2 v3 v4
  = case coe v4 of
      C_lt_44 -> coe du_lookup_218 (coe v0) (coe v3)
      C_eq_46 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      C_gt_48 -> coe du_lookup_218 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.fromList
d_fromList_238 ::
  () -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Map_62
d_fromList_238 ~v0 = du_fromList_238
du_fromList_238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Map_62
du_fromList_238
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v0 ->
            coe
              du_insert_192
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))))
      (coe C_tip_66)
-- Once.CCC.Codegen.StackDepthTable.Row
d_Row_248 = ()
data T_Row_248 = C_row_262 Bool Integer Integer
-- Once.CCC.Codegen.StackDepthTable.Row.r-bnd
d_r'45'bnd_256 :: T_Row_248 -> Bool
d_r'45'bnd_256 v0
  = case coe v0 of
      C_row_262 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Row.r-past
d_r'45'past_258 :: T_Row_248 -> Integer
d_r'45'past_258 v0
  = case coe v0 of
      C_row_262 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Row.r-frame
d_r'45'frame_260 :: T_Row_248 -> Integer
d_r'45'frame_260 v0
  = case coe v0 of
      C_row_262 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.maybe
d_maybe_268 ::
  () ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
d_maybe_268 ~v0 ~v1 v2 v3 v4 = du_maybe_268 v2 v3 v4
du_maybe_268 ::
  AgdaAny -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
du_maybe_268 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v1 v3
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.toDepths
d_toDepths_280 ::
  T_Map_62 ->
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_toDepths_280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_depths_288
      (coe
         (\ v5 ->
            coe
              du_maybe_268 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
              (coe (\ v6 -> d_r'45'bnd_256 (coe v6)))
              (coe du_lookup_218 (coe v0) (coe d_enc'45'entry_36 (coe v5)))))
      (coe
         (\ v5 ->
            coe
              du_maybe_268 (coe (0 :: Integer))
              (coe
                 (\ v6 ->
                    addInt
                      (coe d_r'45'frame_260 (coe v6)) (coe d_r'45'past_258 (coe v6))))
              (coe du_lookup_218 (coe v0) (coe d_enc'45'entry_36 (coe v5)))))
      (coe
         (\ v5 ->
            coe
              du_maybe_268 (coe (0 :: Integer))
              (coe (\ v6 -> d_r'45'past_258 (coe v6)))
              (coe du_lookup_218 (coe v0) (coe d_enc'45'entry_36 (coe v5)))))
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         (\ v5 ->
            coe
              du_maybe_268
              (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
              (coe (\ v6 -> v6))
              (coe du_lookup_218 (coe v4) (coe d_enc'45'label_28 (coe v5)))))
-- Once.CCC.Codegen.StackDepthTable.Op
d_Op_304 = ()
data T_Op_304
  = C_op'45'call_306 [Integer]
                     MAlonzo.Code.Once.CCC.Label.T_EntryId_22 |
    C_op'45'clo_308 | C_op'45'sig_310 Integer
-- Once.CCC.Codegen.StackDepthTable.Seg
d_Seg_312 = ()
data T_Seg_312
  = C_seg_326 MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
              Integer [T_Op_304]
-- Once.CCC.Codegen.StackDepthTable.Seg.sg-own
d_sg'45'own_320 ::
  T_Seg_312 -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
d_sg'45'own_320 v0
  = case coe v0 of
      C_seg_326 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Seg.sg-frame
d_sg'45'frame_322 :: T_Seg_312 -> Integer
d_sg'45'frame_322 v0
  = case coe v0 of
      C_seg_326 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Seg.sg-ops
d_sg'45'ops_324 :: T_Seg_312 -> [T_Op_304]
d_sg'45'ops_324 v0
  = case coe v0 of
      C_seg_326 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.op-of
d_op'45'of_328 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 ->
  Maybe T_Op_304
d_op'45'of_328 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe C_op'45'call_306 (coe d_enc'45'entry_36 (coe v2)) (coe v2))
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_op'45'clo_308)
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'sig_66 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe C_op'45'sig_310 (coe v2))
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepthTable.segments
d_segments_334 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [T_Seg_312]
d_segments_334 v0
  = coe
      d_go_342 (coe v0) (coe v0)
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_342 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer -> [T_Op_304] -> [T_Seg_312] -> [T_Seg_312]
d_go_342 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_seg_326 (coe v2) (coe v3) (coe v4)) (coe v5)
      (:) v6 v7
        -> coe
             d_at_374 (coe v0) (coe v6) (coe v7) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.o′
d_o'8242'_368 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
d_o'8242'_368 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 = du_o'8242'_368 v1 v3
du_o'8242'_368 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
du_o'8242'_368 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v1)
      (coe v0)
-- Once.CCC.Codegen.StackDepthTable._._.more
d_more_370 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] -> [T_Seg_312] -> Maybe T_Op_304 -> [T_Op_304]
d_more_370 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_more_370 v5 v7
du_more_370 :: [T_Op_304] -> Maybe T_Op_304 -> [T_Op_304]
du_more_370 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v0)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.at
d_at_374 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> [T_Seg_312]
d_at_374 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe
                 MAlonzo.Code.Once.CCC.Codegen.StackDepth.d__'8801''7495''7484'__42
                 (coe du_o'8242'_368 (coe v1) (coe v3)) (coe v3))
              (coe
                 d_go_342 (coe v0) (coe v2) (coe v3) (coe v4)
                 (coe du_more_370 (coe v5) (coe d_op'45'of_328 (coe v7))) (coe v6))
              (coe
                 d_go_342 (coe v0) (coe v2) (coe du_o'8242'_368 (coe v1) (coe v3))
                 (coe (0 :: Integer))
                 (coe du_single_386 (coe d_op'45'of_328 (coe v7)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe C_seg_326 (coe v3) (coe v4) (coe v5)) (coe v6))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v9 v10
           -> coe
                d_go_342 (coe v0) (coe v2) (coe du_o'8242'_368 (coe v1) (coe v3))
                (coe v10) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe C_seg_326 (coe v3) (coe v4) (coe v5)) (coe v6))
         _ -> coe v8)
-- Once.CCC.Codegen.StackDepthTable._._._.single
d_single_386 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 ->
  Maybe T_Op_304 -> [T_Op_304]
d_single_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_single_386 v8
du_single_386 :: Maybe T_Op_304 -> [T_Op_304]
du_single_386 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.seg-map
d_seg'45'map_390 :: [T_Seg_312] -> T_Map_62
d_seg'45'map_390 v0
  = case coe v0 of
      [] -> coe C_tip_66
      (:) v1 v2
        -> case coe v1 of
             C_seg_326 v3 v4 v5
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
                      -> coe d_seg'45'map_390 (coe v2)
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v6
                      -> coe
                           du_insert_192 (coe d_enc'45'entry_36 (coe v6)) (coe v1)
                           (coe d_seg'45'map_390 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.RSt
d_RSt_408 = ()
data T_RSt_408 = C_r'45'busy_410 | C_r'45'fin_412 Bool
-- Once.CCC.Codegen.StackDepthTable.reach
d_reach_414 ::
  Integer ->
  T_Map_62 ->
  [Integer] -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reach_414 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_by_438 (coe v4) (coe v1) (coe v2) (coe v3)
                (coe du_lookup_218 (coe v3) (coe v2)))
-- Once.CCC.Codegen.StackDepthTable.reach-ops
d_reach'45'ops_416 ::
  Integer ->
  T_Map_62 ->
  [T_Op_304] -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reach'45'ops_416 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)
      (:) v4 v5
        -> case coe v4 of
             C_op'45'call_306 v6 v7
               -> coe
                    du_more_506 (coe v0) (coe v1) (coe v5)
                    (coe d_reach_414 (coe v0) (coe v1) (coe v6) (coe v3))
             C_op'45'clo_308
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v3)
             C_op'45'sig_310 v6
               -> coe d_reach'45'ops_416 (coe v0) (coe v1) (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.reach-seg
d_reach'45'seg_418 ::
  Integer ->
  T_Map_62 ->
  [Integer] ->
  Maybe T_Seg_312 ->
  T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_reach'45'seg_418 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             C_seg_326 v6 v7 v8
               -> coe
                    du_fin_464 (coe v2)
                    (coe d_reach'45'ops_416 (coe v0) (coe v1) (coe v8) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe
                du_insert_192 (coe v2)
                (coe C_r'45'fin_412 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.by
d_by_438 ::
  Integer ->
  T_Map_62 ->
  [Integer] ->
  T_Map_62 ->
  Maybe T_RSt_408 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_by_438 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             C_r'45'busy_410
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3)
             C_r'45'fin_412 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_reach'45'seg_418 (coe v0) (coe v1) (coe v2)
             (coe du_lookup_218 (coe v1) (coe v2))
             (coe du_insert_192 (coe v2) (coe C_r'45'busy_410) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.fin
d_fin_464 ::
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_464 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 = du_fin_464 v2 v7
du_fin_464 ::
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_464 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe du_insert_192 (coe v0) (coe C_r'45'fin_412 (coe v2)) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.more
d_more_506 ::
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Op_304] ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_more_506 v0 v1 ~v2 ~v3 v4 ~v5 v6 = du_more_506 v0 v1 v4 v6
du_more_506 ::
  Integer ->
  T_Map_62 ->
  [T_Op_304] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_more_506 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> if coe v4
             then coe v3
             else coe d_reach'45'ops_416 (coe v0) (coe v1) (coe v2) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.clo-cycle
d_clo'45'cycle_512 :: Integer -> [T_Seg_312] -> T_Map_62 -> Bool
d_clo'45'cycle_512 v0 v1 v2
  = coe d_go_524 (coe v0) (coe v1) (coe v2) (coe v1) (coe C_tip_66)
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_524 ::
  Integer ->
  [T_Seg_312] -> T_Map_62 -> [T_Seg_312] -> T_Map_62 -> Bool
d_go_524 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v5 v6
        -> case coe v5 of
             C_seg_326 v7 v8 v9
               -> let v10
                        = d_go_524 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v11
                         -> case coe v11 of
                              MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v12
                                -> coe
                                     du_any_538 (coe v0) (coe v1) (coe v2) (coe v6)
                                     (coe
                                        d_reach_414 (coe v0) (coe v2)
                                        (coe d_enc'45'entry_36 (coe v11)) (coe v4))
                              _ -> coe v10
                       _ -> coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.any
d_any_538 ::
  Integer ->
  [T_Seg_312] ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] ->
  T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_any_538 v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8
  = du_any_538 v0 v1 v2 v6 v8
du_any_538 ::
  Integer ->
  [T_Seg_312] ->
  T_Map_62 ->
  [T_Seg_312] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
du_any_538 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> if coe v5
             then coe v5
             else coe d_go_524 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.d-max
d_d'45'max_546 :: Integer
d_d'45'max_546 = coe (4096 :: Integer)
-- Once.CCC.Codegen.StackDepthTable.DSt
d_DSt_548 = ()
data T_DSt_548 = C_d'45'busy_550 Bool | C_d'45'fin_552 T_Row_248
-- Once.CCC.Codegen.StackDepthTable.depth
d_depth_554 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_depth_554 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v5)
      _ -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_by_586 (coe v6) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe du_lookup_218 (coe v5) (coe v4)))
-- Once.CCC.Codegen.StackDepthTable.depth-seg
d_depth'45'seg_556 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Seg_312 -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_depth'45'seg_556 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      C_seg_326 v8 v9 v10
        -> coe
             du_fin_626 (coe v4) (coe v9)
             (coe
                d_depth'45'ops_558 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                (coe v10) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.depth-ops
d_depth'45'ops_558 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Op_304] -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_depth'45'ops_558 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe v6)
      (:) v7 v8
        -> coe
             du_one_696 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.by
d_by_586 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  T_Map_62 ->
  Maybe T_DSt_548 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_by_586 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             C_d'45'busy_550 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                    (coe
                       du_insert_192 (coe v4)
                       (coe
                          C_d'45'busy_550 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                       (coe v5))
             C_d'45'fin_552 v8
               -> case coe v8 of
                    C_row_262 v9 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v9)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe addInt (coe v10) (coe v11)))
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_from_598 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe du_lookup_218 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.from
d_from_598 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  T_Map_62 ->
  Maybe T_Seg_312 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from_598 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             C_seg_326 v8 v9 v10
               -> case coe v8 of
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
                           (coe v5)
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v11
                      -> coe
                           d_depth'45'seg_556 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v11) (coe v7)
                           (coe
                              du_insert_192 (coe v4)
                              (coe
                                 C_d'45'busy_550 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                              (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.fin
d_fin_626 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fin_626 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 v10
  = du_fin_626 v4 v7 v10
du_fin_626 ::
  [Integer] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fin_626 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             du_done_640 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe du_lookup_218 (coe v4) (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.cut
d_cut_636 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  T_Map_62 -> Integer -> T_Map_62 -> Maybe T_DSt_548 -> Bool
d_cut_636 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_cut_636 v12
du_cut_636 :: Maybe T_DSt_548 -> Bool
du_cut_636 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_d'45'busy_550 v3 -> coe v3
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepthTable._._.done
d_done_640 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Integer ->
  [T_Op_304] ->
  T_Map_62 ->
  Integer ->
  T_Map_62 ->
  Maybe T_DSt_548 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_done_640 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_done_640 v4 v7 v10 v11 v12
du_done_640 ::
  [Integer] ->
  Integer ->
  Integer ->
  T_Map_62 ->
  Maybe T_DSt_548 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_done_640 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               MAlonzo.Code.Data.Bool.Base.d_not_22 (coe du_cut_636 (coe v4)))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
               (coe addInt (coe v1) (coe v2)) (coe d_d'45'max_546)))
         (coe
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
            (coe addInt (coe v1) (coe v2)))
         (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (coe
         du_insert_192 (coe v0)
         (coe
            C_d'45'fin_552
            (coe
               C_row_262
               (coe
                  MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                  (coe
                     MAlonzo.Code.Data.Bool.Base.d_not_22 (coe du_cut_636 (coe v4)))
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                     (coe addInt (coe v1) (coe v2)) (coe d_d'45'max_546)))
               (coe v2) (coe v1)))
         (coe v3))
-- Once.CCC.Codegen.StackDepthTable._.rest
d_rest_678 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Op_304 ->
  [T_Op_304] ->
  T_Map_62 ->
  Integer -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rest_678 v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9
  = du_rest_678 v0 v1 v2 v3 v4 v6 v8 v9
du_rest_678 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Op_304] ->
  Integer -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rest_678 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_add_688 (coe v6)
      (coe
         d_depth'45'ops_558 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v7))
-- Once.CCC.Codegen.StackDepthTable._._.add
d_add_688 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Op_304 ->
  [T_Op_304] ->
  T_Map_62 ->
  Integer ->
  T_Map_62 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_add_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_add_688 v10 v11
du_add_688 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_add_688 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.one
d_one_696 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Op_304 ->
  [T_Op_304] ->
  T_Map_62 -> T_Op_304 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_one_696 v0 v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_one_696 v0 v1 v2 v3 v4 v6 v7 v8
du_one_696 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Op_304] ->
  T_Map_62 -> T_Op_304 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_one_696 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_op'45'call_306 v8 v9
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7473'__228 (coe v9)
                (coe v4))
             (coe
                du_rest_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe (0 :: Integer)) (coe v6))
             (coe
                du_call_708 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe
                   d_depth_554 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v6)))
      C_op'45'clo_308
        -> coe
             du_rest_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
                (coe (0 :: Integer)) (coe addInt (coe (1 :: Integer)) (coe v2)))
             (coe v6)
      C_op'45'sig_310 v8
        -> coe
             du_rest_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v8) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.call
d_call_708 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Op_304 ->
  [T_Op_304] ->
  T_Map_62 ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call_708 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 v10
  = du_call_708 v0 v1 v2 v3 v4 v6 v10
du_call_708 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Op_304] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call_708 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    du_rest_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v8)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_rest_678 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe (0 :: Integer)) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.start-ops
d_start'45'ops_716 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [T_Seg_312] -> T_Map_62 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_start'45'ops_716 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe v5)
      (:) v6 v7
        -> case coe v6 of
             C_seg_326 v8 v9 v10
               -> let v11
                        = d_start'45'ops_716
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v5) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
                         -> coe
                              du_both_746 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                              (coe
                                 d_depth'45'ops_558 (coe v0) (coe v1) (coe v2) (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26
                                    (coe
                                       MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                 (coe v10) (coe v5))
                       _ -> coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.both
d_both_746 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_both_746 v0 v1 v2 v3 ~v4 ~v5 v6 ~v7 v8
  = du_both_746 v0 v1 v2 v3 v6 v8
du_both_746 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  [T_Seg_312] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_both_746 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             du_more_756 (coe v6)
             (coe
                d_start'45'ops_716 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.more
d_more_756 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] ->
  T_Map_62 ->
  Integer ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_more_756 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10
  = du_more_756 v8 v10
du_more_756 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_more_756 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.all-entries
d_all'45'entries_774 ::
  Integer ->
  Bool ->
  Integer -> T_Map_62 -> Bool -> [T_Seg_312] -> T_Map_62 -> T_Map_62
d_all'45'entries_774 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      [] -> coe v6
      (:) v7 v8
        -> coe
             du_one_816 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
             (coe v6) (coe d_sg'45'own_320 (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.visit
d_visit_808 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Bool ->
  T_Seg_312 ->
  [T_Seg_312] ->
  T_Map_62 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> T_Map_62
d_visit_808 v0 v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_visit_808 v0 v1 v2 v3 v4 v6 v7 v8
du_visit_808 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Bool ->
  [T_Seg_312] ->
  T_Map_62 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> T_Map_62
du_visit_808 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_all'45'entries_774 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            d_depth_554 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
            (coe v2) (coe v3) (coe d_enc'45'entry_36 (coe v7)) (coe v6)))
-- Once.CCC.Codegen.StackDepthTable._.one
d_one_816 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Bool ->
  T_Seg_312 ->
  [T_Seg_312] ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 -> T_Map_62
d_one_816 v0 v1 v2 v3 v4 ~v5 v6 v7 v8
  = du_one_816 v0 v1 v2 v3 v4 v6 v7 v8
du_one_816 ::
  Integer ->
  Bool ->
  Integer ->
  T_Map_62 ->
  Bool ->
  [T_Seg_312] ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 -> T_Map_62
du_one_816 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
        -> coe
             d_all'45'entries_774 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v8
        -> case coe v8 of
             MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v9
               -> coe
                    du_visit_808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v8)
             MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v4)
                    (coe
                       d_all'45'entries_774 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6))
                    (coe
                       du_visit_808 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.clo-max
d_clo'45'max_822 :: [T_Seg_312] -> T_Map_62 -> Integer
d_clo'45'max_822 v0 v1
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v2 v3
        -> case coe v2 of
             C_seg_326 v4 v5 v6
               -> let v7 = d_clo'45'max_822 (coe v3) (coe v1) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v8
                         -> case coe v8 of
                              MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v9
                                -> coe
                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                     (coe
                                        du_at_836
                                        (coe
                                           du_lookup_218 (coe v1) (coe d_enc'45'entry_36 (coe v8))))
                                     (coe d_clo'45'max_822 (coe v3) (coe v1))
                              _ -> coe v7
                       _ -> coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.at
d_at_836 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [T_Op_304] -> [T_Seg_312] -> T_Map_62 -> Maybe T_DSt_548 -> Integer
d_at_836 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_at_836 v5
du_at_836 :: Maybe T_DSt_548 -> Integer
du_at_836 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                C_d'45'fin_552 v3
                  -> case coe v3 of
                       C_row_262 v4 v5 v6 -> coe addInt (coe v5) (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepthTable.rows-of
d_rows'45'of_846 :: [T_Seg_312] -> T_Map_62 -> T_Map_62
d_rows'45'of_846 v0 v1
  = case coe v0 of
      [] -> coe C_tip_66
      (:) v2 v3
        -> case coe v2 of
             C_seg_326 v4 v5 v6
               -> case coe v4 of
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
                      -> coe d_rows'45'of_846 (coe v3) (coe v1)
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v7
                      -> coe
                           du_at_860 (coe v7) (coe v3) (coe v1)
                           (coe du_lookup_218 (coe v1) (coe d_enc'45'entry_36 (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.at
d_at_860 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  [T_Op_304] ->
  [T_Seg_312] -> T_Map_62 -> Maybe T_DSt_548 -> T_Map_62
d_at_860 v0 ~v1 ~v2 v3 v4 v5 = du_at_860 v0 v3 v4 v5
du_at_860 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [T_Seg_312] -> T_Map_62 -> Maybe T_DSt_548 -> T_Map_62
du_at_860 v0 v1 v2 v3
  = let v4 = d_rows'45'of_846 (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> case coe v5 of
                C_d'45'fin_552 v6
                  -> coe
                       du_insert_192 (coe d_enc'45'entry_36 (coe v0)) (coe v6)
                       (coe d_rows'45'of_846 (coe v1) (coe v2))
                _ -> coe v4
         _ -> coe v4)
-- Once.CCC.Codegen.StackDepthTable.labels
d_labels_868 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62
d_labels_868 v0
  = coe
      du_go_876
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
      (coe v0) (coe C_tip_66)
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_876 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 -> T_Map_62
d_go_876 ~v0 v1 v2 v3 = du_go_876 v1 v2 v3
du_go_876 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 -> T_Map_62
du_go_876 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             du_go_876
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v0)
                (coe v3))
             (coe v4)
             (coe
                du_add_894 (coe v0) (coe v3) (coe v2)
                (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_82 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.add
d_add_894 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> T_Map_62
d_add_894 ~v0 v1 v2 ~v3 v4 v5 = du_add_894 v1 v2 v4 v5
du_add_894 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> T_Map_62
du_add_894 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'label_70 v4
        -> coe
             du_insert_192 (coe d_enc'45'label_28 (coe v4))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_124 (coe v0)
                (coe v1))
             (coe v2)
      _ -> coe v2
-- Once.CCC.Codegen.StackDepthTable.table
d_table_898 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_table_898 v0
  = coe
      d_build_912 (coe v0)
      (coe
         d_clo'45'cycle_512 (coe d_fuel_910 (coe v0))
         (coe d_ss_906 (coe v0)) (coe d_sm_908 (coe v0)))
-- Once.CCC.Codegen.StackDepthTable._.ss
d_ss_906 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [T_Seg_312]
d_ss_906 v0 = coe d_segments_334 (coe v0)
-- Once.CCC.Codegen.StackDepthTable._.sm
d_sm_908 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62
d_sm_908 v0 = coe d_seg'45'map_390 (coe d_ss_906 (coe v0))
-- Once.CCC.Codegen.StackDepthTable._.fuel
d_fuel_910 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer
d_fuel_910 v0
  = coe
      addInt (coe (1 :: Integer))
      (coe MAlonzo.Code.Data.List.Base.du_length_268 (d_ss_906 (coe v0)))
-- Once.CCC.Codegen.StackDepthTable._.build
d_build_912 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_build_912 v0 v1
  = coe
      d_finish_924 (coe v0) (coe v1)
      (coe
         d_all'45'entries_774 (coe d_fuel_910 (coe v0)) (coe v1)
         (coe d_cd_922 (coe v0) (coe v1)) (coe d_sm_908 (coe v0))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe d_ss_906 (coe v0)) (coe d_m'8321'_920 (coe v0) (coe v1)))
-- Once.CCC.Codegen.StackDepthTable._._.m₁
d_m'8321'_920 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool -> T_Map_62
d_m'8321'_920 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
      (coe C_tip_66)
      (coe
         d_all'45'entries_774 (coe d_fuel_910 (coe v0)) (coe v1)
         (coe (0 :: Integer)) (coe d_sm_908 (coe v0))
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe d_ss_906 (coe v0)) (coe C_tip_66))
-- Once.CCC.Codegen.StackDepthTable._._.cd
d_cd_922 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool -> Integer
d_cd_922 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v1)
      (coe (0 :: Integer))
      (coe
         d_clo'45'max_822 (coe d_ss_906 (coe v0))
         (coe d_m'8321'_920 (coe v0) (coe v1)))
-- Once.CCC.Codegen.StackDepthTable._._.finish
d_finish_924 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool ->
  T_Map_62 -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_finish_924 v0 v1 v2
  = coe
      du_from_932 (coe v0) (coe v1)
      (coe
         d_start'45'ops_716 (coe d_fuel_910 (coe v0)) (coe v1)
         (coe d_cd_922 (coe v0) (coe v1)) (coe d_sm_908 (coe v0))
         (coe d_ss_906 (coe v0)) (coe v2))
-- Once.CCC.Codegen.StackDepthTable._._._.from
d_from_932 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool ->
  T_Map_62 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
d_from_932 v0 v1 ~v2 v3 = du_from_932 v0 v1 v3
du_from_932 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_254
du_from_932 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             d_toDepths_280
             (coe d_rows'45'of_846 (coe d_ss_906 (coe v0)) (coe v4)) (coe v3)
             (coe v1) (coe d_clo'45'max_822 (coe d_ss_906 (coe v0)) (coe v4))
             (coe d_labels_868 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
