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
d_Tm_96 a0 a1 a2 a3 a4 = ()
-- Once.Measure.Copies.cells
d_cells_636 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_cells_636 ~v0 v1 = du_cells_636 v1
du_cells_636 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
du_cells_636 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_636 (coe v1)) (coe du_cells_636 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_cells_636 (coe v1)) (coe du_cells_636 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe du_cells_636 (coe v2)
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
d_Copies_648 a0 = ()
data T_Copies_648 = C_copies_662 Integer Integer Integer
-- Once.Measure.Copies.Copies.dups
d_dups_656 :: T_Copies_648 -> Integer
d_dups_656 v0
  = case coe v0 of
      C_copies_662 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.dup-cells
d_dup'45'cells_658 :: T_Copies_648 -> Integer
d_dup'45'cells_658 v0
  = case coe v0 of
      C_copies_662 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.Copies.bcopy-cells
d_bcopy'45'cells_660 :: T_Copies_648 -> Integer
d_bcopy'45'cells_660 v0
  = case coe v0 of
      C_copies_662 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.none
d_none_664 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> T_Copies_648
d_none_664 ~v0 = du_none_664
du_none_664 :: T_Copies_648
du_none_664
  = coe
      C_copies_662 (coe (0 :: Integer)) (coe (0 :: Integer))
      (coe (0 :: Integer))
-- Once.Measure.Copies._⊞_
d__'8862'__666 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Copies_648 -> T_Copies_648 -> T_Copies_648
d__'8862'__666 ~v0 v1 v2 = du__'8862'__666 v1 v2
du__'8862'__666 :: T_Copies_648 -> T_Copies_648 -> T_Copies_648
du__'8862'__666 v0 v1
  = case coe v0 of
      C_copies_662 v2 v3 v4
        -> case coe v1 of
             C_copies_662 v5 v6 v7
               -> coe
                    C_copies_662 (coe addInt (coe v2) (coe v5))
                    (coe addInt (coe v3) (coe v6)) (coe addInt (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.bump
d_bump_680 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Integer -> Integer
d_bump_680 ~v0 v1 v2 = du_bump_680 v1 v2
du_bump_680 :: Bool -> Integer -> Integer
du_bump_680 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v1)
-- Once.Measure.Copies.tm
d_tm_694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_648
d_tm_694 ~v0 ~v1 v2 v3 v4 v5 = du_tm_694 v2 v3 v4 v5
du_tm_694 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> T_Copies_648
du_tm_694 v0 v1 v2 v3
  = let v4 = coe du_none_664 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                du__'8862'__666 (coe du_tm_694 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_tm_694 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              du__'8862'__666
                              (coe du_tm_694 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_tm_694 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_dup_866
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
                  -> coe
                       C_copies_662 (coe (1 :: Integer))
                       (coe du_bump_680 (coe du_cells_636 (coe v1)) (coe (0 :: Integer)))
                       (coe (0 :: Integer))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__666
                       (coe du_tm_694 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_tm_694 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcata_924 v8
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_694 (coe v0)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v2))
                       (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lend_966 v9
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                         -> coe
                              du_tm_694
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_974 v8
           -> coe
                du_tm_694 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1)
                (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_984 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_694 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_tm_694 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1004 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       du__'8862'__666
                       (coe du_tm_694 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_tm_694 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1012 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_tm_694
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016
           -> coe
                C_copies_662 (coe (0 :: Integer)) (coe (0 :: Integer))
                (coe du_bump_680 (coe du_cells_636 (coe v0)) (coe (0 :: Integer)))
         MAlonzo.Code.Once.LinCore.Core.C_llam_1042 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_tm_694 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω_1056 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe du_tm_694 (coe v1) (coe v14) (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_llamω'7580'_1088 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v12 v13 v14 v15
                  -> coe
                       du_tm_694 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v14))
                       (coe v15) (coe v10)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1134 v8 v9
           -> coe
                du_tm_694 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.Measure.Copies.body
d_body_742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_1784 -> T_Copies_648
d_body_742 ~v0 ~v1 v2 v3 = du_body_742 v2 v3
du_body_742 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_1784 -> T_Copies_648
du_body_742 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_b1_1798 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe
                    du_tm_694 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v10) (coe v11))
                    (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_bω_1810 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C_sg_726 v8 v9 v10 v11 v12
               -> coe du_tm_694 (coe v10) (coe v11) (coe v12) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.defs
d_defs_750 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1812 -> T_Copies_648
d_defs_750 ~v0 v1 v2 = du_defs_750 v1 v2
du_defs_750 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1812 -> T_Copies_648
du_defs_750 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_ε_1814 -> coe du_none_664
      MAlonzo.Code.Once.LinCore.Core.C__'9656'__1820 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v6 v7
               -> coe
                    du__'8862'__666 (coe du_defs_750 (coe v6) (coe v4))
                    (coe du_body_742 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Measure.Copies.show-copies
d_show'45'copies_756 ::
  T_Copies_648 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show'45'copies_756 v0
  = case coe v0 of
      C_copies_662 v1 v2 v3
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
                         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
