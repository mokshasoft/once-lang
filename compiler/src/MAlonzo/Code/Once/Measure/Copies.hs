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

module MAlonzo.Code.Once.Measure.Copies where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Measure.Copies._.Body
d_Body_32 a0 a1 a2 = ()
-- Once.Measure.Copies._.Defs
d_Defs_42 a0 a1 = ()
-- Once.Measure.Copies._.LTy
d_LTy_72 a0 = ()
-- Once.Measure.Copies._.Tm
d_Tm_100 a0 a1 a2 a3 a4 = ()
-- Once.Measure.Copies.cells
d_cells_724 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_cells_724 ~v0 v1 = du_cells_724 v1
du_cells_724 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
du_cells_724 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_724 (coe v1)) (coe du_cells_724 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_724 (coe v1)) (coe du_cells_724 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_cells_724 (coe v2)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies
d_Copies_736 a0 = ()
data T_Copies_736 = C_copies_754 Integer Integer Integer Integer
-- Once.Measure.Copies.Copies.dups
d_dups_746 :: T_Copies_736 -> Integer
d_dups_746 v0
  = case coe v0 of
      C_copies_754 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.dup-cells
d_dup'45'cells_748 :: T_Copies_736 -> Integer
d_dup'45'cells_748 v0
  = case coe v0 of
      C_copies_754 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.bcopy-cells
d_bcopy'45'cells_750 :: T_Copies_736 -> Integer
d_bcopy'45'cells_750 v0
  = case coe v0 of
      C_copies_754 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.clo-cells
d_clo'45'cells_752 :: T_Copies_736 -> Integer
d_clo'45'cells_752 v0
  = case coe v0 of
      C_copies_754 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.none
d_none_756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_Copies_736
d_none_756 ~v0 = du_none_756
du_none_756 :: T_Copies_736
du_none_756
  = coe
      C_copies_754 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Measure.Copies._⊞_
d__'8862'__758 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Copies_736 -> T_Copies_736 -> T_Copies_736
d__'8862'__758 ~v0 v1 v2 = du__'8862'__758 v1 v2
du__'8862'__758 :: T_Copies_736 -> T_Copies_736 -> T_Copies_736
du__'8862'__758 v0 v1
  = case coe v0 of
      C_copies_754 v2 v3 v4 v5
        -> case coe v1 of
             C_copies_754 v6 v7 v8 v9
               -> coe
                    C_copies_754 (coe addInt (coe v2) (coe v6))
                    (coe addInt (coe v3) (coe v7)) (coe addInt (coe v4) (coe v8))
                    (coe addInt (coe v5) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.bump
d_bump_776 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Integer -> Integer
d_bump_776 ~v0 v1 v2 = du_bump_776 v1 v2
du_bump_776 :: Bool -> Integer -> Integer
du_bump_776 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v1)
-- Once.Measure.Copies.tm
d_tm_790 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_736
d_tm_790 ~v0 ~v1 v2 v3 v4 v5 = du_tm_790 v2 v3 v4 v5
du_tm_790 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_736
du_tm_790 v0 v1 v2 v3
  = let v4 = coe du_none_756 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                du__'8862'__758 (coe du_tm_790 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_tm_790 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              du__'8862'__758
                              (coe du_tm_790 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_tm_790 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_dup_866
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
                  -> coe
                       C_copies_754 (coe (1 :: Integer))
                       (coe du_bump_776 (coe du_cells_724 (coe v1)) (coe (0 :: Integer)))
                       (coe (0 :: Integer)) (coe (0 :: Integer))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__758
                       (coe du_tm_790 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_tm_790 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_790 (coe v0)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v2))
                       (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lend_976 v9
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                         -> coe
                              du_tm_790
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_tm_790 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1)
                (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_790 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_790 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__758
                       (coe du_tm_790 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_tm_790 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_790
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026
           -> coe
                C_copies_754 (coe (0 :: Integer)) (coe (0 :: Integer))
                (coe du_bump_776 (coe du_cells_724 (coe v0)) (coe (0 :: Integer)))
                (coe (0 :: Integer))
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_tm_790 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_tm_790 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du__'8862'__758
                       (coe
                          C_copies_754 (coe (0 :: Integer)) (coe (0 :: Integer))
                          (coe (0 :: Integer))
                          (coe du_bump_776 (coe du_cells_724 (coe v1)) (coe (0 :: Integer))))
                       (coe
                          du_tm_790 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_tm_790 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.body
d_body_840 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 -> T_Copies_736
d_body_840 ~v0 ~v1 v2 v3 = du_body_840 v2 v3
du_body_840 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 -> T_Copies_736
du_body_840 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_tm_790 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_tm_790 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.defs
d_defs_848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 -> T_Copies_736
d_defs_848 ~v0 v1 v2 = du_defs_848 v1 v2
du_defs_848 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 -> T_Copies_736
du_defs_848 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364 -> coe du_none_756
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    du__'8862'__758 (coe du_defs_848 (coe v6) (coe v4))
                    (coe du_body_840 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.showT
d_showT_854 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showT_854 ~v0 v1 = du_showT_854 v1
du_showT_854 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showT_854 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe ("1" :: Data.Text.Text)
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe ("0" :: Data.Text.Text)
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_showT_854 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("*" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_showT_854 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_showT_854 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("+" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_showT_854 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("C" :: Data.Text.Text) (coe du_showT_854 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v1 v2 v3 v4
        -> coe ("Fn" :: Data.Text.Text)
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v1
        -> coe ("Nu" :: Data.Text.Text)
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v1
        -> coe ("Mu" :: Data.Text.Text)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v1
        -> coe ("w" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.headOf
d_headOf_874 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_headOf_874 ~v0 ~v1 ~v2 v3 v4 v5 = du_headOf_874 v3 v4 v5
du_headOf_874 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_headOf_874 v0 v1 v2
  = let v3 = "_" :: Data.Text.Text in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.LinCore.Core.C_lid_786
           -> coe ("id" :: Data.Text.Text)
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v5 v8 v9
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_headOf_874 (coe v5) (coe v1) (coe v8))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("." :: Data.Text.Text)
                   (coe du_headOf_874 (coe v0) (coe v5) (coe v9)))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v13 v14
                         -> coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("<" :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (coe du_headOf_874 (coe v11) (coe v13) (coe v9))
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("|" :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       (coe du_headOf_874 (coe v12) (coe v14) (coe v10))
                                       (">" :: Data.Text.Text))))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.LinCore.Core.C_lassoc_842
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                         -> case coe v1 of
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                                -> case coe v13 of
                                     MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                                       -> coe ("a" :: Data.Text.Text)
                                     _ -> coe v3
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.LinCore.Core.C_lapp_966 v5 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
                  -> case coe v11 of
                       MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v13 v14
                         -> coe ("app" :: Data.Text.Text)
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.LinCore.Core.C_lunf_1116
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v9 v10 v11 v12
                         -> case coe v1 of
                              MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v13
                                -> coe ("unf" :: Data.Text.Text)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         _ -> coe v3)
-- Once.Measure.Copies.sitesT
d_sitesT_892 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sitesT_892 ~v0 ~v1 v2 v3 v4 v5 = du_sitesT_892 v2 v3 v4 v5
du_sitesT_892 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_sitesT_892 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_sitesT_892 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_sitesT_892 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe du_sitesT_892 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_sitesT_892 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_sitesT_892 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_sitesT_892 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_sitesT_892 (coe v0)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v2))
                       (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lend_976 v9
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                         -> coe
                              du_sitesT_892
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_sitesT_892 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                (coe v1) (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_sitesT_892 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_sitesT_892 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_sitesT_892 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_sitesT_892 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_sitesT_892
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_sitesT_892 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_sitesT_892 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe du_cells_724 (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (coe du_showT_854 (coe v1))
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (":" :: Data.Text.Text)
                                   (coe
                                      du_headOf_874
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1)
                                         (coe v14))
                                      (coe v15) (coe v10))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          du_sitesT_892 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_sitesT_892 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.sitesB
d_sitesB_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sitesB_938 ~v0 ~v1 v2 v3 = du_sitesB_938 v2 v3
du_sitesB_938 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_sitesB_938 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_sitesT_892 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_sitesT_892 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.clo-sites
d_clo'45'sites_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_clo'45'sites_946 ~v0 v1 v2 = du_clo'45'sites_946 v1 v2
du_clo'45'sites_946 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_clo'45'sites_946 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_clo'45'sites_946 (coe v6) (coe v4))
                    (coe du_sitesB_938 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.show-sites
d_show'45'sites_952 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'sites_952 ~v0 v1 = du_show'45'sites_952 v1
du_show'45'sites_952 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'sites_952 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("clo-sites:" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.List.Base.du_foldr_216
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                 (" " :: Data.Text.Text)
                 (coe MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1 v2)))
         (coe ("" :: Data.Text.Text)) (coe v0))
-- Once.Measure.Copies.show-copies
d_show'45'copies_960 ::
  T_Copies_736 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'copies_960 v0
  = case coe v0 of
      C_copies_754 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("copies: dups=" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" dup-cells=" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" bcopy-cells=" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (" clo-cells=" :: Data.Text.Text)
                               (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)))))))
      _ -> MAlonzo.RTE.mazUnreachableError
