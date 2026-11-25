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
  T_Map_62 -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_toDepths_280 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_depths_296
      (coe
         (\ v5 ->
            coe
              du_maybe_268 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
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
      (coe v1) (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v2))
      (coe v3) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         (\ v5 ->
            coe
              du_maybe_268
              (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
              (coe (\ v6 -> v6))
              (coe du_lookup_218 (coe v4) (coe d_enc'45'label_28 (coe v5)))))
-- Once.CCC.Codegen.StackDepthTable.call-ok
d_call'45'ok_304 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> Bool
d_call'45'ok_304 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'call_62 v4
           -> coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d__'8801''7495''7484'__42
                   (coe v1)
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 (coe v4)))
                (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_bnd_280 v0 v4)
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'clo_64
           -> coe
                MAlonzo.Code.Data.Bool.Base.d_not_22
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_clo'45'chk_288 (coe v0))
         _ -> coe v3)
-- Once.CCC.Codegen.StackDepthTable.Scan
d_Scan_320 = ()
data T_Scan_320
  = C_scan_334 MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
               T_Row_248 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.CCC.Codegen.StackDepthTable.Scan.s-own
d_s'45'own_328 ::
  T_Scan_320 -> MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
d_s'45'own_328 v0
  = case coe v0 of
      C_scan_334 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Scan.s-row
d_s'45'row_330 :: T_Scan_320 -> T_Row_248
d_s'45'row_330 v0
  = case coe v0 of
      C_scan_334 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Scan.s-done
d_s'45'done_332 ::
  T_Scan_320 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_s'45'done_332 v0
  = case coe v0 of
      C_scan_334 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.flush
d_flush_336 ::
  T_Scan_320 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_flush_336 v0
  = case coe v0 of
      C_scan_334 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.step
d_step_344 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  T_Scan_320 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  T_Scan_320
d_step_344 v0 v1 v2
  = case coe v1 of
      C_scan_334 v3 v4 v5
        -> case coe v4 of
             C_row_262 v6 v7 v8
               -> coe
                    d_go_368 (coe v0) (coe v3) (coe v6) (coe v7) (coe v8) (coe v5)
                    (coe v2)
                    (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_78 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.o′
d_o'8242'_364 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Bool ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
d_o'8242'_364 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 = du_o'8242'_364 v1 v6
du_o'8242'_364 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36
du_o'8242'_364 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_114 (coe v0)
      (coe v1)
-- Once.CCC.Codegen.StackDepthTable._.c
d_c_366 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Bool ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  Integer
d_c_366 v0 v1 ~v2 ~v3 ~v4 ~v5 v6 = du_c_366 v0 v1 v6
du_c_366 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  Integer
du_c_366 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_cost_352 (coe v0)
      (coe du_o'8242'_364 (coe v1) (coe v2)) (coe v2)
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_368 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Bool ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> T_Scan_320
d_go_368 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              C_scan_334 (coe v1)
              (coe
                 C_row_262
                 (coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v2)
                    (coe
                       d_call'45'ok_304 (coe v0) (coe du_o'8242'_364 (coe v1) (coe v6))
                       (coe v7)))
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                    (coe du_c_366 (coe v0) (coe v1) (coe v6)))
                 (coe v4))
              (coe v5) in
    coe
      (case coe v7 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v9 v10
           -> coe
                C_scan_334 (coe du_o'8242'_364 (coe v1) (coe v6))
                (coe
                   C_row_262 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                   (coe du_c_366 (coe v0) (coe v1) (coe v6)) (coe v10))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                      (coe C_row_262 (coe v2) (coe v3) (coe v4)))
                   (coe v5))
         _ -> coe v8)
-- Once.CCC.Codegen.StackDepthTable.rows
d_rows_376 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_rows_376 v0 v1
  = coe
      d_flush_336
      (coe
         du_go_386 (coe v0) (coe v1)
         (coe
            C_scan_334
            (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
            (coe
               C_row_262 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
               (coe (0 :: Integer)) (coe (0 :: Integer)))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_386 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Scan_320 -> T_Scan_320
d_go_386 v0 ~v1 v2 v3 = du_go_386 v0 v2 v3
du_go_386 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Scan_320 -> T_Scan_320
du_go_386 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             du_go_386 (coe v0) (coe v4)
             (coe d_step_344 (coe v0) (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Summary
d_Summary_396 = ()
data T_Summary_396 = C_summary_414 T_Map_62 Integer Bool Integer
-- Once.CCC.Codegen.StackDepthTable.Summary.m-rows
d_m'45'rows_406 :: T_Summary_396 -> T_Map_62
d_m'45'rows_406 v0
  = case coe v0 of
      C_summary_414 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Summary.m-p₀
d_m'45'p'8320'_408 :: T_Summary_396 -> Integer
d_m'45'p'8320'_408 v0
  = case coe v0 of
      C_summary_414 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Summary.m-clo-b
d_m'45'clo'45'b_410 :: T_Summary_396 -> Bool
d_m'45'clo'45'b_410 v0
  = case coe v0 of
      C_summary_414 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.Summary.m-clo-d
d_m'45'clo'45'd_412 :: T_Summary_396 -> Integer
d_m'45'clo'45'd_412 v0
  = case coe v0 of
      C_summary_414 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.summarize
d_summarize_416 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_Summary_396
d_summarize_416 v0
  = case coe v0 of
      []
        -> coe
             C_summary_414 (coe C_tip_66) (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe (0 :: Integer))
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38
                      -> coe du_add_426 (coe v4) (coe d_summarize_416 (coe v2))
                    MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'entry_40 v5
                      -> coe du_add_448 (coe v4) (coe v5) (coe d_summarize_416 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.add
d_add_426 ::
  T_Row_248 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Summary_396 -> T_Summary_396
d_add_426 v0 ~v1 v2 = du_add_426 v0 v2
du_add_426 :: T_Row_248 -> T_Summary_396 -> T_Summary_396
du_add_426 v0 v1
  = case coe v1 of
      C_summary_414 v2 v3 v4 v5
        -> coe
             C_summary_414 (coe v2)
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe d_r'45'past_258 (coe v0)) (coe v3))
             (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.dep
d_dep_446 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Row_248 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer
d_dep_446 ~v0 v1 ~v2 = du_dep_446 v1
du_dep_446 :: T_Row_248 -> Integer
du_dep_446 v0
  = coe
      addInt (coe d_r'45'frame_260 (coe v0))
      (coe d_r'45'past_258 (coe v0))
-- Once.CCC.Codegen.StackDepthTable._.add
d_add_448 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Row_248 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Summary_396 -> T_Summary_396
d_add_448 ~v0 v1 ~v2 v3 v4 = du_add_448 v1 v3 v4
du_add_448 ::
  T_Row_248 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  T_Summary_396 -> T_Summary_396
du_add_448 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v3
        -> case coe v2 of
             C_summary_414 v4 v5 v6 v7
               -> coe
                    C_summary_414
                    (coe
                       du_insert_192 (coe d_enc'45'entry_36 (coe v1)) (coe v0) (coe v4))
                    (coe v5)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v6)
                       (coe d_r'45'bnd_256 (coe v0)))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe du_dep_446 (coe v0))
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v3
        -> case coe v2 of
             C_summary_414 v4 v5 v6 v7
               -> coe
                    C_summary_414
                    (coe
                       du_insert_192 (coe d_enc'45'entry_36 (coe v1)) (coe v0) (coe v4))
                    (coe v5) (coe v6) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable.labels
d_labels_470 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62
d_labels_470 v0
  = coe
      du_go_478
      (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38)
      (coe v0) (coe C_tip_66)
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_478 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 -> T_Map_62
d_go_478 ~v0 v1 v2 v3 = du_go_478 v1 v2 v3
du_go_478 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 -> T_Map_62
du_go_478 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             du_go_478
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_114 (coe v0)
                (coe v3))
             (coe v4)
             (coe
                du_add_496 (coe v0) (coe v3) (coe v2)
                (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_78 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._._.add
d_add_496 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> T_Map_62
d_add_496 ~v0 v1 v2 ~v3 v4 v5 = du_add_496 v1 v2 v4 v5
du_add_496 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  T_Map_62 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> T_Map_62
du_add_496 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'label_70 v4
        -> coe
             du_insert_192 (coe d_enc'45'label_28 (coe v4))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_own_114 (coe v0)
                (coe v1))
             (coe v2)
      _ -> coe v2
-- Once.CCC.Codegen.StackDepthTable.same-rows
d_same'45'rows_500 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
d_same'45'rows_500 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         []
           -> case coe v1 of
                [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         (:) v3 v4
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       C_row_262 v7 v8 v9
                         -> case coe v1 of
                              (:) v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                       -> case coe v13 of
                                            C_row_262 v14 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Codegen.StackDepth.d__'8801''7495''7484'__42
                                                      (coe v5) (coe v12))
                                                   (coe
                                                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                                      (coe
                                                         du__'8801''7495''7470'__526 (coe v7)
                                                         (coe v14))
                                                      (coe
                                                         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                                         (coe eqInt (coe v8) (coe v15))
                                                         (coe
                                                            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                                            (coe eqInt (coe v9) (coe v16))
                                                            (coe
                                                               d_same'45'rows_500 (coe v4)
                                                               (coe v11)))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v2
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Codegen.StackDepthTable._._≡ᵇᴮ_
d__'8801''7495''7470'__526 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Bool ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Owner_36 ->
  Bool ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool -> Bool -> Bool
d__'8801''7495''7470'__526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10 v11
  = du__'8801''7495''7470'__526 v10 v11
du__'8801''7495''7470'__526 :: Bool -> Bool -> Bool
du__'8801''7495''7470'__526 v0 v1
  = if coe v0
      then coe v1
      else coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v1)
-- Once.CCC.Codegen.StackDepthTable.entries
d_entries_532 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer
d_entries_532 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe
             addInt
             (coe
                du_go_542
                (coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.d_kind_78 (coe v1)))
             (coe d_entries_532 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.go
d_go_542 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> Integer
d_go_542 ~v0 ~v1 v2 = du_go_542 v2
du_go_542 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Kind_60 -> Integer
du_go_542 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_k'45'entry_68 v2 v3
           -> coe (1 :: Integer)
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepthTable.table
d_table_544 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_table_544 v0
  = coe
      du_iter_582 (coe v0)
      (coe addInt (coe (2 :: Integer)) (coe d_entries_532 (coe v0)))
      (coe d_rows_376 (coe du_T'45'init_572) (coe v0))
-- Once.CCC.Codegen.StackDepthTable._.lm
d_lm_552 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Map_62
d_lm_552 v0 = coe d_labels_470 (coe v0)
-- Once.CCC.Codegen.StackDepthTable._.of
d_of_554 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_of_554 v0 v1
  = coe du_go_562 (coe v0) (coe d_summarize_416 (coe v1))
-- Once.CCC.Codegen.StackDepthTable._._.go
d_go_562 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Summary_396 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_go_562 v0 ~v1 v2 = du_go_562 v0 v2
du_go_562 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Summary_396 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
du_go_562 v0 v1
  = case coe v1 of
      C_summary_414 v2 v3 v4 v5
        -> coe
             d_toDepths_280 (coe v2) (coe v3) (coe v4) (coe v5)
             (coe d_lm_552 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepthTable._.T-init
d_T'45'init_572 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_T'45'init_572 ~v0 = du_T'45'init_572
du_T'45'init_572 ::
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
du_T'45'init_572
  = coe
      MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_depths_296
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe (\ v0 -> 0 :: Integer)) (coe (\ v0 -> 0 :: Integer))
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe (0 :: Integer)) (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         (\ v0 ->
            coe MAlonzo.Code.Once.CCC.Codegen.StackDepth.C_o'45'start_38))
-- Once.CCC.Codegen.StackDepthTable._.iter
d_iter_582 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_iter_582 v0 v1 ~v2 v3 = du_iter_582 v0 v1 v3
du_iter_582 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
du_iter_582 v0 v1 v2
  = case coe v1 of
      0 -> coe d_of_554 (coe v0) (coe v2)
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du_next_598 (coe v0) (coe v3) (coe v2)
                (coe d_of_554 (coe v0) (coe v2)))
-- Once.CCC.Codegen.StackDepthTable._._.next
d_next_598 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_next_598 v0 v1 ~v2 v3 v4 = du_next_598 v0 v1 v3 v4
du_next_598 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
du_next_598 v0 v1 v2 v3
  = coe
      du_stop_606 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_rows_376 (coe v3) (coe v0))
-- Once.CCC.Codegen.StackDepthTable._._._.stop
d_stop_606 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
d_stop_606 v0 v1 ~v2 v3 v4 v5 = du_stop_606 v0 v1 v3 v4 v5
du_stop_606 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CCC.Codegen.StackDepth.T_Depths_262
du_stop_606 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe d_same'45'rows_500 (coe v2) (coe v4)) (coe v3)
      (coe du_iter_582 (coe v0) (coe v1) (coe v4))
