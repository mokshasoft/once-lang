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

module MAlonzo.Code.Once.LinCore.CopyFree where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.CopyFree._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.CopyFree._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.CopyFree._.Tm
d_Tm_100 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.CopyFree.cells
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
-- Once.LinCore.CopyFree.NC
d_NC_736 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> ()
d_NC_736 = erased
-- Once.LinCore.CopyFree._.CF
d_CF_754 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> ()
d_CF_754 = erased
-- Once.LinCore.CopyFree.nc-∨
d_nc'45''8744'_810 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d_nc'45''8744'_810 ~v0 v1 v2 ~v3 ~v4 = du_nc'45''8744'_810 v1 v2
du_nc'45''8744'_810 :: Bool -> Bool -> AgdaAny
du_nc'45''8744'_810 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.T-∧
d_T'45''8743'_816 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_T'45''8743'_816 ~v0 v1 v2 ~v3 = du_T'45''8743'_816 v1 v2
du_T'45''8743'_816 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_T'45''8743'_816 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.LinCore.CopyFree.not-∨ʳ
d_not'45''8744''691'_822 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny
d_not'45''8744''691'_822 ~v0 v1 v2 ~v3
  = du_not'45''8744''691'_822 v1 v2
du_not'45''8744''691'_822 :: Bool -> Bool -> AgdaAny
du_not'45''8744''691'_822 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.not-∨ˡ
d_not'45''8744''737'_828 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny
d_not'45''8744''737'_828 ~v0 v1 v2 ~v3
  = du_not'45''8744''737'_828 v1 v2
du_not'45''8744''737'_828 :: Bool -> Bool -> AgdaAny
du_not'45''8744''737'_828 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.notnot
d_notnot_832 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> AgdaAny -> AgdaAny
d_notnot_832 ~v0 v1 ~v2 = du_notnot_832 v1
du_notnot_832 :: Bool -> AgdaAny
du_notnot_832 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
