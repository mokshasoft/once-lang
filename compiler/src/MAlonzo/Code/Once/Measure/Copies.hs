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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.TyEq
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Measure.Copies._.Body
d_Body_36 a0 a1 a2 = ()
-- Once.Measure.Copies._.Defs
d_Defs_46 a0 a1 = ()
-- Once.Measure.Copies._.Kd
d_Kd_62 a0 = ()
-- Once.Measure.Copies._.LTy
d_LTy_76 a0 = ()
-- Once.Measure.Copies._.Own
d_Own_94 a0 a1 a2 a3 a4 a5 = ()
-- Once.Measure.Copies._.Tm
d_Tm_104 a0 a1 a2 a3 a4 = ()
-- Once.Measure.Copies.cells
d_cells_728 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_cells_728 ~v0 v1 = du_cells_728 v1
du_cells_728 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
du_cells_728 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_728 (coe v1)) (coe du_cells_728 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_728 (coe v1)) (coe du_cells_728 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_cells_728 (coe v2)
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
d_Copies_740 a0 = ()
data T_Copies_740 = C_copies_758 Integer Integer Integer Integer
-- Once.Measure.Copies.Copies.dups
d_dups_750 :: T_Copies_740 -> Integer
d_dups_750 v0
  = case coe v0 of
      C_copies_758 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.dup-cells
d_dup'45'cells_752 :: T_Copies_740 -> Integer
d_dup'45'cells_752 v0
  = case coe v0 of
      C_copies_758 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.bcopy-cells
d_bcopy'45'cells_754 :: T_Copies_740 -> Integer
d_bcopy'45'cells_754 v0
  = case coe v0 of
      C_copies_758 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.clo-cells
d_clo'45'cells_756 :: T_Copies_740 -> Integer
d_clo'45'cells_756 v0
  = case coe v0 of
      C_copies_758 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.none
d_none_760 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_Copies_740
d_none_760 ~v0 = du_none_760
du_none_760 :: T_Copies_740
du_none_760
  = coe
      C_copies_758 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Measure.Copies._⊞_
d__'8862'__762 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Copies_740 -> T_Copies_740 -> T_Copies_740
d__'8862'__762 ~v0 v1 v2 = du__'8862'__762 v1 v2
du__'8862'__762 :: T_Copies_740 -> T_Copies_740 -> T_Copies_740
du__'8862'__762 v0 v1
  = case coe v0 of
      C_copies_758 v2 v3 v4 v5
        -> case coe v1 of
             C_copies_758 v6 v7 v8 v9
               -> coe
                    C_copies_758 (coe addInt (coe v2) (coe v6))
                    (coe addInt (coe v3) (coe v7)) (coe addInt (coe v4) (coe v8))
                    (coe addInt (coe v5) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.bump
d_bump_780 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Integer -> Integer
d_bump_780 ~v0 v1 v2 = du_bump_780 v1 v2
du_bump_780 :: Bool -> Integer -> Integer
du_bump_780 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v1)
-- Once.Measure.Copies.tm
d_tm_794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_740
d_tm_794 ~v0 ~v1 v2 v3 v4 v5 = du_tm_794 v2 v3 v4 v5
du_tm_794 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_740
du_tm_794 v0 v1 v2 v3
  = let v4 = coe du_none_760 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                du__'8862'__762 (coe du_tm_794 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_tm_794 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              du__'8862'__762
                              (coe du_tm_794 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_tm_794 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_dup_866
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
                  -> coe
                       C_copies_758 (coe (1 :: Integer))
                       (coe du_bump_780 (coe du_cells_728 (coe v1)) (coe (0 :: Integer)))
                       (coe (0 :: Integer)) (coe (0 :: Integer))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__762
                       (coe du_tm_794 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_tm_794 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_794 (coe v0)
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
                              du_tm_794
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_tm_794 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1)
                (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_794 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_794 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__762
                       (coe du_tm_794 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_tm_794 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_794
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026
           -> coe
                C_copies_758 (coe (0 :: Integer)) (coe (0 :: Integer))
                (coe du_bump_780 (coe du_cells_728 (coe v0)) (coe (0 :: Integer)))
                (coe (0 :: Integer))
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_tm_794 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_tm_794 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du__'8862'__762
                       (coe
                          C_copies_758 (coe (0 :: Integer)) (coe (0 :: Integer))
                          (coe (0 :: Integer))
                          (coe du_bump_780 (coe du_cells_728 (coe v1)) (coe (0 :: Integer))))
                       (coe
                          du_tm_794 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_tm_794 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.body
d_body_844 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 -> T_Copies_740
d_body_844 ~v0 ~v1 v2 v3 = du_body_844 v2 v3
du_body_844 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 -> T_Copies_740
du_body_844 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_tm_794 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_tm_794 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.defs
d_defs_852 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 -> T_Copies_740
d_defs_852 ~v0 v1 v2 = du_defs_852 v1 v2
du_defs_852 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 -> T_Copies_740
du_defs_852 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364 -> coe du_none_760
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    du__'8862'__762 (coe du_defs_852 (coe v6) (coe v4))
                    (coe du_body_844 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.showT
d_showT_858 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showT_858 ~v0 v1 = du_showT_858 v1
du_showT_858 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showT_858 v0
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
                (coe du_showT_858 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("*" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_showT_858 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_showT_858 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("+" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_showT_858 (coe v2)) (")" :: Data.Text.Text))))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("C" :: Data.Text.Text) (coe du_showT_858 (coe v2))
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
d_headOf_878 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_headOf_878 ~v0 ~v1 ~v2 v3 v4 v5 = du_headOf_878 v3 v4 v5
du_headOf_878 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_headOf_878 v0 v1 v2
  = let v3 = "_" :: Data.Text.Text in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.LinCore.Core.C_lid_786
           -> coe ("id" :: Data.Text.Text)
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v5 v8 v9
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_headOf_878 (coe v5) (coe v1) (coe v8))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("." :: Data.Text.Text)
                   (coe du_headOf_878 (coe v0) (coe v5) (coe v9)))
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
                                 (coe du_headOf_878 (coe v11) (coe v13) (coe v9))
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("|" :: Data.Text.Text)
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       (coe du_headOf_878 (coe v12) (coe v14) (coe v10))
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
d_sitesT_896 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sitesT_896 ~v0 ~v1 v2 v3 v4 v5 = du_sitesT_896 v2 v3 v4 v5
du_sitesT_896 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_sitesT_896 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_sitesT_896 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_sitesT_896 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe du_sitesT_896 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_sitesT_896 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_sitesT_896 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_sitesT_896 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_sitesT_896 (coe v0)
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
                              du_sitesT_896
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_sitesT_896 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                (coe v1) (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_sitesT_896 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_sitesT_896 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_sitesT_896 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_sitesT_896 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_sitesT_896
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_sitesT_896 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_sitesT_896 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe du_cells_728 (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (coe du_showT_858 (coe v1))
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (":" :: Data.Text.Text)
                                   (coe
                                      du_headOf_878
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1)
                                         (coe v14))
                                      (coe v15) (coe v10))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe
                          du_sitesT_896 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_sitesT_896 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.sitesB
d_sitesB_942 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_sitesB_942 ~v0 ~v1 v2 v3 = du_sitesB_942 v2 v3
du_sitesB_942 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_sitesB_942 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_sitesT_896 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_sitesT_896 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.clo-sites
d_clo'45'sites_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_clo'45'sites_950 ~v0 v1 v2 = du_clo'45'sites_950 v1 v2
du_clo'45'sites_950 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_clo'45'sites_950 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe du_clo'45'sites_950 (coe v6) (coe v4))
                    (coe du_sitesB_942 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.show-sites
d_show'45'sites_956 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'sites_956 ~v0 v1 = du_show'45'sites_956 v1
du_show'45'sites_956 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show'45'sites_956 v0
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
-- Once.Measure.Copies.Fact
d_Fact_964 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Fact_964 = erased
-- Once.Measure.Copies.under?
d_under'63'_966 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_under'63'_966 ~v0 v1 = du_under'63'_966 v1
du_under'63'_966 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_under'63'_966 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
                -> case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v1
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v3)
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Measure.Copies.facts
d_facts_986 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_facts_986 v0 v1 v2 v3 v4 v5
  = let v6 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v8 v11 v12
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_facts_986 (coe v0) (coe v1) (coe v2) (coe v8) (coe v4) (coe v11))
                (coe
                   d_facts_986 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v12))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v12 v13
           -> case coe v3 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                  -> case coe v4 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v16 v17
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 d_facts_986 (coe v0) (coe v1) (coe v2) (coe v14) (coe v16)
                                 (coe v12))
                              (coe
                                 d_facts_986 (coe v0) (coe v1) (coe v2) (coe v15) (coe v17)
                                 (coe v13))
                       _ -> coe v6
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v11 v12
           -> case coe v3 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v13 v14
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_facts_986 (coe v0) (coe v1) (coe v2) (coe v13) (coe v4)
                          (coe v11))
                       (coe
                          d_facts_986 (coe v0) (coe v1) (coe v2) (coe v14) (coe v4)
                          (coe v12))
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v10
           -> case coe v3 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                  -> coe
                       d_facts_986 (coe v0) (coe v1) (coe v2)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v11) (coe v4))
                       (coe v4) (coe v10)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_lend_976 v11
           -> case coe v3 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v4 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              d_facts_986 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v2) (coe v12))
                              (coe v13) (coe v15) (coe v11)
                       _ -> coe v6
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v10
           -> coe
                d_facts_986 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v3) (coe v4)
                (coe v10)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> coe
                       d_facts_986 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4) (coe v11)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> coe
                       d_facts_986 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4) (coe v11)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v11 v12
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v13 v14
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_facts_986 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                          (coe v11))
                       (coe
                          d_facts_986 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                          (coe v12))
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v10
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                  -> coe
                       d_facts_986 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v11) (coe v2))
                       (coe v3) (coe v4) (coe v10)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v12 v13
           -> case coe v4 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v14 v15 v16 v17
                  -> coe
                       d_facts_986 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v3) (coe v16))
                       (coe v17) (coe v12)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v12 v13
           -> case coe v4 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v14 v15 v16 v17
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          du_under'63'_966
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v15) (coe v16)
                             (coe v17))
                          (d_facts_986
                             (coe v0) (coe v1) (coe v3) (coe v16) (coe v17) (coe v12)))
                       (coe
                          d_factsO_998 (coe v0) (coe v1) (coe v3) (coe v16) (coe v17)
                          (coe v12)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.d_ownOf_2216 (coe v0) (coe v1)
                             (coe v3) (coe v16) (coe v17) (coe v12)))
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_bev_1084
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v10 v11 v12 v13
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v11) (coe v3)
                             (coe v4)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v12 v13
           -> case coe v4 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v14 v15 v16 v17
                  -> coe
                       d_facts_986 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v3) (coe v16))
                       (coe v17) (coe v12)
                _ -> coe v6
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v10 v11
           -> coe
                d_facts_986 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v4) (coe v3))
                (coe v10)
         _ -> coe v6)
-- Once.Measure.Copies.factsO
d_factsO_998 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_factsO_998 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.LinCore.Core.C_o'45'bg_1892
        -> coe
             d_facts_986 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.LinCore.Core.C_o'45'ev_1900
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fst_1912 v12
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v19
                      -> coe
                           d_factsO_998 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                           (coe v19) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'snd_1924 v12
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v19
                      -> coe
                           d_factsO_998 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                           (coe v19) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'split_1940 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v19 v22 v23
                      -> case coe v22 of
                           MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v28
                             -> case coe v23 of
                                  MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v33
                                    -> coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            d_factsO_998 (coe v0) (coe v1) (coe v16) (coe v19)
                                            (coe v4) (coe v28) (coe v14))
                                         (coe
                                            d_factsO_998 (coe v0) (coe v1) (coe v17) (coe v3)
                                            (coe v19) (coe v33) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'case_1954 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v21 v22
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_factsO_998 (coe v0) (coe v1) (coe v2) (coe v15) (coe v4)
                              (coe v21) (coe v13))
                           (coe
                              d_factsO_998 (coe v0) (coe v1) (coe v2) (coe v16) (coe v4)
                              (coe v22) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fork_1976 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v19 v20
               -> case coe v4 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v21 v22
                      -> case coe v5 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v24 v27 v28
                             -> case coe v24 of
                                  MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v29 v30
                                    -> case coe v27 of
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v36 v37
                                           -> case coe v36 of
                                                MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v42
                                                  -> case coe v37 of
                                                       MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v47
                                                         -> coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 d_factsO_998 (coe v0) (coe v1)
                                                                 (coe v19) (coe v29) (coe v21)
                                                                 (coe v42) (coe v17))
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                 (coe
                                                                    d_factsO_998 (coe v0) (coe v1)
                                                                    (coe v20) (coe v30) (coe v22)
                                                                    (coe v47) (coe v18))
                                                                 (coe
                                                                    d_facts_986 (coe v0) (coe v1)
                                                                    (coe v2) (coe v3) (coe v24)
                                                                    (coe v28)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'lift_1990 v13
        -> case coe v5 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v15 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.LinCore.Core.C_blift_984 v23
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_facts_986 (coe v0) (coe v1)
                              (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v15) (coe v4)
                              (coe v23))
                           (coe
                              d_factsO_998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                              (coe v19) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'pre_2004 v13
        -> case coe v5 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v15 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Once.LinCore.Core.C_blift_984 v23
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_factsO_998 (coe v0) (coe v1) (coe v2) (coe v15) (coe v4)
                              (coe v18) (coe v13))
                           (coe
                              d_facts_986 (coe v0) (coe v1)
                              (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v3) (coe v15)
                              (coe v23))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.factsB
d_factsB_1102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_factsB_1102 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v10 v11 v12 v13 v14
               -> coe
                    d_facts_986 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v12) (coe v13))
                    (coe v14) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v10 v11 v12 v13 v14
               -> coe
                    d_facts_986 (coe v0) (coe v1) (coe v12) (coe v13) (coe v14)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.factsD
d_factsD_1110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_factsD_1110 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_factsD_1110 (coe v0) (coe v7) (coe v5))
                    (coe d_factsB_1102 (coe v0) (coe v7) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.elemT
d_elemT_1116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
d_elemT_1116 ~v0 v1 = du_elemT_1116 v1
du_elemT_1116 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
du_elemT_1116 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
              (coe
                 MAlonzo.Code.Once.LinCore.TyEq.du_eqT_1106 (coe v0) (coe v1))))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Once.Measure.Copies.stepL
d_stepL_1124 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_stepL_1124 ~v0 v1 v2 = du_stepL_1124 v1 v2
du_stepL_1124 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_stepL_1124 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v2 v3 ->
            case coe v2 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                -> case coe v4 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                       -> coe
                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                            (coe
                               MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe du_elemT_1116 v6 v1)
                               (coe
                                  MAlonzo.Code.Data.Bool.Base.d_not_22 (coe du_elemT_1116 v5 v3)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v3))
                            (coe v3)
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                            (coe du_elemT_1116 v5 v3) (coe v3)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v3))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe v1) (coe v0)
-- Once.Measure.Copies.iter
d_iter_1142 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_iter_1142 ~v0 v1 v2 v3 = du_iter_1142 v1 v2 v3
du_iter_1142 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_iter_1142 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_iter_1142 (coe v3) (coe v1)
                (coe du_stepL_1124 (coe v1) (coe v2)))
-- Once.Measure.Copies.closT
d_closT_1162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_closT_1162 ~v0 ~v1 v2 v3 v4 v5 = du_closT_1162 v2 v3 v4 v5
du_closT_1162 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_closT_1162 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_closT_1162 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_closT_1162 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe du_closT_1162 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_closT_1162 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_closT_1162 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_closT_1162 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_closT_1162 (coe v0)
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
                              du_closT_1162
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_closT_1162 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                (coe v1) (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_closT_1162 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_closT_1162 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_closT_1162 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_closT_1162 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_closT_1162
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_closT_1162 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v13) (coe v14)
                             (coe v15))
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                       (coe du_closT_1162 (coe v1) (coe v14) (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v13) (coe v14)
                             (coe v15))
                          (coe du_cells_728 (coe v1)))
                       (coe
                          du_closT_1162 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_closT_1162 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.closD
d_closD_1220 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_closD_1220 ~v0 v1 v2 = du_closD_1220 v1 v2
du_closD_1220 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_closD_1220 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2364
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2370 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> case coe v5 of
                    MAlonzo.Code.Once.LinCore.Core.C_b1_2348 v12 v13
                      -> case coe v7 of
                           MAlonzo.Code.Once.LinCore.Core.C_sg_726 v14 v15 v16 v17 v18
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe du_closD_1220 (coe v6) (coe v4))
                                  (coe
                                     du_closT_1162 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v16)
                                        (coe v17))
                                     (coe v18) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.LinCore.Core.C_bω_2360 v12 v13
                      -> case coe v7 of
                           MAlonzo.Code.Once.LinCore.Core.C_sg_726 v14 v15 v16 v17 v18
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe du_closD_1220 (coe v6) (coe v4))
                                  (coe du_closT_1162 (coe v16) (coe v17) (coe v18) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.count
d_count_1232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Integer
d_count_1232 ~v0 ~v1 v2 = du_count_1232 v2
du_count_1232 :: (AgdaAny -> Bool) -> [AgdaAny] -> Integer
du_count_1232 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v1)
              (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v2)))
      (coe (0 :: Integer))
-- Once.Measure.Copies.lent-reach
d_lent'45'reach_1242 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lent'45'reach_1242 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("lent-entries: total=" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe
            MAlonzo.Code.Data.Nat.Show.d_show_56
            (coe
               MAlonzo.Code.Data.List.Base.du_length_268
               (coe du_cs_1254 (coe v1) (coe v2))))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (" pruned=" :: Data.Text.Text)
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (coe
                  MAlonzo.Code.Data.Nat.Show.d_show_56
                  (coe
                     du_count_1232
                     (\ v3 ->
                        MAlonzo.Code.Data.Bool.Base.d_not_22
                          (coe
                             du_elemT_1116 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                             (d_l_1252 (coe v0) (coe v1) (coe v2))))
                     (coe du_cs_1254 (coe v1) (coe v2))))
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (" copying=" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (coe
                        MAlonzo.Code.Data.Nat.Show.d_show_56
                        (coe
                           du_count_1232
                           (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                           (coe du_cs_1254 (coe v1) (coe v2))))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" copying-pruned=" :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.Nat.Show.d_show_56
                           (coe
                              du_count_1232
                              (\ v3 ->
                                 MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                                   (coe
                                      MAlonzo.Code.Data.Bool.Base.d_not_22
                                      (coe
                                         du_elemT_1116
                                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                                         (d_l_1252 (coe v0) (coe v1) (coe v2)))))
                              (coe du_cs_1254 (coe v1) (coe v2))))))))))
-- Once.Measure.Copies._.fs
d_fs_1250 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_fs_1250 v0 v1 v2 = coe d_factsD_1110 (coe v0) (coe v1) (coe v2)
-- Once.Measure.Copies._.l
d_l_1252 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_l_1252 v0 v1 v2
  = coe
      du_iter_1142
      (coe
         addInt (coe (1 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (d_fs_1250 (coe v0) (coe v1) (coe v2))))
      (coe d_fs_1250 (coe v0) (coe v1) (coe v2))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Measure.Copies._.cs
d_cs_1254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cs_1254 ~v0 v1 v2 = du_cs_1254 v1 v2
du_cs_1254 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_cs_1254 v0 v1 = coe du_closD_1220 (coe v0) (coe v1)
-- Once.Measure.Copies.show-copies
d_show'45'copies_1260 ::
  T_Copies_740 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'copies_1260 v0
  = case coe v0 of
      C_copies_758 v1 v2 v3 v4
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
