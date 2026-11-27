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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
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
d_Tm_98 a0 a1 a2 a3 a4 = ()
-- Once.Measure.Copies.cells
d_cells_686 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_cells_686 ~v0 v1 = du_cells_686 v1
du_cells_686 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
du_cells_686 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_686 (coe v1)) (coe du_cells_686 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_686 (coe v1)) (coe du_cells_686 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_cells_686 (coe v2)
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
d_Copies_698 a0 = ()
data T_Copies_698 = C_copies_716 Integer Integer Integer Integer
-- Once.Measure.Copies.Copies.dups
d_dups_708 :: T_Copies_698 -> Integer
d_dups_708 v0
  = case coe v0 of
      C_copies_716 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.dup-cells
d_dup'45'cells_710 :: T_Copies_698 -> Integer
d_dup'45'cells_710 v0
  = case coe v0 of
      C_copies_716 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.bcopy-cells
d_bcopy'45'cells_712 :: T_Copies_698 -> Integer
d_bcopy'45'cells_712 v0
  = case coe v0 of
      C_copies_716 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.clo-cells
d_clo'45'cells_714 :: T_Copies_698 -> Integer
d_clo'45'cells_714 v0
  = case coe v0 of
      C_copies_716 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.none
d_none_718 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_Copies_698
d_none_718 ~v0 = du_none_718
du_none_718 :: T_Copies_698
du_none_718
  = coe
      C_copies_716 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.Measure.Copies._⊞_
d__'8862'__720 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Copies_698 -> T_Copies_698 -> T_Copies_698
d__'8862'__720 ~v0 v1 v2 = du__'8862'__720 v1 v2
du__'8862'__720 :: T_Copies_698 -> T_Copies_698 -> T_Copies_698
du__'8862'__720 v0 v1
  = case coe v0 of
      C_copies_716 v2 v3 v4 v5
        -> case coe v1 of
             C_copies_716 v6 v7 v8 v9
               -> coe
                    C_copies_716 (coe addInt (coe v2) (coe v6))
                    (coe addInt (coe v3) (coe v7)) (coe addInt (coe v4) (coe v8))
                    (coe addInt (coe v5) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.bump
d_bump_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Integer -> Integer
d_bump_738 ~v0 v1 v2 = du_bump_738 v1 v2
du_bump_738 :: Bool -> Integer -> Integer
du_bump_738 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v1)
-- Once.Measure.Copies.tm
d_tm_752 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_698
d_tm_752 ~v0 ~v1 v2 v3 v4 v5 = du_tm_752 v2 v3 v4 v5
du_tm_752 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_698
du_tm_752 v0 v1 v2 v3
  = let v4 = coe du_none_718 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                du__'8862'__720 (coe du_tm_752 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_tm_752 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              du__'8862'__720
                              (coe du_tm_752 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_tm_752 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_dup_866
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
                  -> coe
                       C_copies_716 (coe (1 :: Integer))
                       (coe du_bump_738 (coe du_cells_686 (coe v1)) (coe (0 :: Integer)))
                       (coe (0 :: Integer)) (coe (0 :: Integer))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__720
                       (coe du_tm_752 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_tm_752 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_934 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_752 (coe v0)
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
                              du_tm_752
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_tm_752 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1)
                (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_752 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_752 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__720
                       (coe du_tm_752 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_tm_752 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_752
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026
           -> coe
                C_copies_716 (coe (0 :: Integer)) (coe (0 :: Integer))
                (coe du_bump_738 (coe du_cells_686 (coe v0)) (coe (0 :: Integer)))
                (coe (0 :: Integer))
         MAlonzo.Code.Once.LinCore.Core.C_llam_1052 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_tm_752 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1066 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_tm_752 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1098 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du__'8862'__720
                       (coe
                          C_copies_716 (coe (0 :: Integer)) (coe (0 :: Integer))
                          (coe (0 :: Integer))
                          (coe du_bump_738 (coe du_cells_686 (coe v1)) (coe (0 :: Integer))))
                       (coe
                          du_tm_752 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                          (coe v15) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_tm_752 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.body
d_body_802 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2050 -> T_Copies_698
d_body_802 ~v0 ~v1 v2 v3 = du_body_802 v2 v3
du_body_802 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2050 -> T_Copies_698
du_body_802 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_2064 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_tm_752 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_2076 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_tm_752 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.defs
d_defs_810 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2078 -> T_Copies_698
d_defs_810 ~v0 v1 v2 = du_defs_810 v1 v2
du_defs_810 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2078 -> T_Copies_698
du_defs_810 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_2080 -> coe du_none_718
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__2086 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    du__'8862'__720 (coe du_defs_810 (coe v6) (coe v4))
                    (coe du_body_802 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.show-copies
d_show'45'copies_816 ::
  T_Copies_698 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'copies_816 v0
  = case coe v0 of
      C_copies_716 v1 v2 v3 v4
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
