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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.CopyFree._.Body
d_Body_32 a0 a1 a2 = ()
-- Once.LinCore.CopyFree._.Defs
d_Defs_42 a0 a1 = ()
-- Once.LinCore.CopyFree._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.CopyFree._.LF
d_LF_66 a0 = ()
-- Once.LinCore.CopyFree._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.CopyFree._.Own
d_Own_90 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.CopyFree._.Tm
d_Tm_100 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.CopyFree._.hasId
d_hasId_160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Bool
d_hasId_160 ~v0 = du_hasId_160
du_hasId_160 :: MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Bool
du_hasId_160 = coe MAlonzo.Code.Once.LinCore.Core.du_hasId_1644
-- Once.LinCore.CopyFree._.mapNu
d_mapNu_330 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapNu_330 ~v0 = du_mapNu_330
du_mapNu_330 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapNu_330 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.Core.du_mapNu_1602 v1 v2
-- Once.LinCore.CopyFree._.obsT
d_obsT_352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_obsT_352 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_obsT_1742 (coe v0)
-- Once.LinCore.CopyFree._.ownT
d_ownT_372 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_ownT_372 ~v0 = du_ownT_372
du_ownT_372 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_ownT_372 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.LinCore.Core.du_ownT_2040 v1 v2 v3 v4 v5
-- Once.LinCore.CopyFree._.ownω
d_ownω_374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_ownω_374 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_ownω_2274 (coe v0)
-- Once.LinCore.CopyFree._.strL
d_strL_386 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_strL_386 ~v0 = du_strL_386
du_strL_386 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_strL_386 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.Core.du_strL_1552 v1 v2 v3
-- Once.LinCore.CopyFree._.strO
d_strO_388 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_strO_388 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_strO_1666 (coe v0)
-- Once.LinCore.CopyFree._.strP
d_strP_390 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Bool -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_strP_390 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_strP_1678 (coe v0)
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
-- Once.LinCore.CopyFree.coCopies
d_coCopies_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Bool
d_coCopies_740 ~v0 v1 = du_coCopies_740 v1
du_coCopies_740 :: MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> Bool
du_coCopies_740 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_coCopies_740 (coe v1)) (coe du_coCopies_740 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe MAlonzo.Code.Once.LinCore.Core.du_hasId_1644 (coe v2))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe MAlonzo.Code.Once.LinCore.Core.du_hasId_1644 (coe v1))
                (coe du_coCopies_740 (coe v2)))
             (coe du_coCopies_740 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.CopyFree._.CF
d_CF_768 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> ()
d_CF_768 = erased
-- Once.LinCore.CopyFree._.CFB
d_CFB_826 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2334 -> ()
d_CFB_826 = erased
-- Once.LinCore.CopyFree._.CFD
d_CFD_834 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2362 -> ()
d_CFD_834 = erased
-- Once.LinCore.CopyFree.nc-∨
d_nc'45''8744'_844 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny -> AgdaAny
d_nc'45''8744'_844 ~v0 v1 v2 ~v3 ~v4 = du_nc'45''8744'_844 v1 v2
du_nc'45''8744'_844 :: Bool -> Bool -> AgdaAny
du_nc'45''8744'_844 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.T-∧
d_T'45''8743'_850 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_T'45''8743'_850 ~v0 v1 v2 ~v3 = du_T'45''8743'_850 v1 v2
du_T'45''8743'_850 ::
  Bool -> Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_T'45''8743'_850 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.LinCore.CopyFree.not-∨ʳ
d_not'45''8744''691'_856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny
d_not'45''8744''691'_856 ~v0 v1 v2 ~v3
  = du_not'45''8744''691'_856 v1 v2
du_not'45''8744''691'_856 :: Bool -> Bool -> AgdaAny
du_not'45''8744''691'_856 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.not-∨ˡ
d_not'45''8744''737'_862 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> Bool -> AgdaAny -> AgdaAny
d_not'45''8744''737'_862 ~v0 v1 v2 ~v3
  = du_not'45''8744''737'_862 v1 v2
du_not'45''8744''737'_862 :: Bool -> Bool -> AgdaAny
du_not'45''8744''737'_862 v0 v1
  = coe
      seq (coe v0)
      (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree.notnot
d_notnot_866 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> AgdaAny -> AgdaAny
d_notnot_866 ~v0 v1 ~v2 = du_notnot_866 v1
du_notnot_866 :: Bool -> AgdaAny
du_notnot_866 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.LinCore.CopyFree._.cf-own
d_cf'45'own_886 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 -> AgdaAny -> AgdaAny
d_cf'45'own_886 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_cf'45'own_886 v3 v4 v5 v6 v7 v8
du_cf'45'own_886 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 -> AgdaAny -> AgdaAny
du_cf'45'own_886 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.LinCore.Core.C_o'45'bg_1892
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe v5)
      MAlonzo.Code.Once.LinCore.Core.C_o'45'ev_1900
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fst_1912 v11
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_cf'45'own_886 (coe v12) (coe v1) (coe v2) (coe v18) (coe v11)
                              (coe v5))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'snd_1924 v11
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_cf'45'own_886 (coe v13) (coe v1) (coe v2) (coe v18) (coe v11)
                              (coe v5))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'split_1940 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v18 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v27
                             -> case coe v22 of
                                  MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v32
                                    -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   du_cf'45'own_886 (coe v15) (coe v18) (coe v2)
                                                   (coe v27) (coe v13) (coe v33))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                      (coe
                                                         du_cf'45'own_886 (coe v16) (coe v1)
                                                         (coe v18) (coe v32) (coe v14) (coe v34)))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'case_1954 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v20 v21
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        du_cf'45'own_886 (coe v0) (coe v14) (coe v2) (coe v20)
                                        (coe v12) (coe v22))
                                     (coe
                                        du_cf'45'own_886 (coe v0) (coe v15) (coe v2) (coe v21)
                                        (coe v13) (coe v23)))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fork_1976 v16 v17
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v23 v26 v27
                             -> case coe v23 of
                                  MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v28 v29
                                    -> case coe v26 of
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v35 v36
                                           -> case coe v35 of
                                                MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v41
                                                  -> case coe v36 of
                                                       MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v46
                                                         -> case coe v5 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                -> case coe v47 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                       -> coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  du_cf'45'own_886
                                                                                  (coe v18)
                                                                                  (coe v28)
                                                                                  (coe v20)
                                                                                  (coe v41)
                                                                                  (coe v16)
                                                                                  (coe v49))
                                                                               (coe
                                                                                  du_cf'45'own_886
                                                                                  (coe v19)
                                                                                  (coe v29)
                                                                                  (coe v21)
                                                                                  (coe v46)
                                                                                  (coe v17)
                                                                                  (coe v50)))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                                               (coe v48))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'lift_1990 v12
        -> case coe v3 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19)
                           (coe
                              du_cf'45'own_886 (coe v0) (coe v1) (coe v14) (coe v18) (coe v12)
                              (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'pre_2004 v12
        -> case coe v3 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_cf'45'own_886 (coe v0) (coe v14) (coe v2) (coe v17) (coe v12)
                              (coe v19))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.CopyFree._.cf-ownω
d_cf'45'ownω_948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> AgdaAny -> AgdaAny
d_cf'45'ownω_948 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_cf'45'ownω_948 v0 v2 v3 v4 v5 v6 v7
du_cf'45'ownω_948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> AgdaAny -> AgdaAny
du_cf'45'ownω_948 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cf'45'own_886 (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.LinCore.Core.d_ownOf_2216 (coe v0) (coe v1)
         (coe v2) (coe v3) (coe v4) (coe v5))
      (coe v6)
-- Once.LinCore.CopyFree._.cf-cin
d_cf'45'cin_964 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cf'45'cin_964 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_cf'45'cin_964 v7 v8
du_cf'45'cin_964 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cf'45'cin_964 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.LinCore.CopyFree._.cf-strL
d_cf'45'strL_980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> AgdaAny -> AgdaAny
d_cf'45'strL_980 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_cf'45'strL_980 v4
du_cf'45'strL_980 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> AgdaAny
du_cf'45'strL_980 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v1
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe du_cf'45'strL_980 (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe du_cf'45'strL_980 (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_cf'45'strL_980 (coe v1)) (coe du_cf'45'strL_980 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.CopyFree._.cf-strO
d_cf'45'strO_1042 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> AgdaAny -> AgdaAny
d_cf'45'strO_1042 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      d_cf'45'strO_1042 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                      (coe v5)
                      (coe
                         du_not'45''8744''737'_862 (coe du_coCopies_740 (coe v7))
                         (coe du_coCopies_740 (coe v8)))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe
                      d_cf'45'strO_1042 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                      (coe v5)
                      (coe
                         du_not'45''8744''691'_856 (coe du_coCopies_740 (coe v7))
                         (coe du_coCopies_740 (coe v8))))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v7 v8
        -> coe
             du_cf'45'strP_1056 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
             (coe v8) (coe v5)
             (coe MAlonzo.Code.Once.LinCore.Core.du_hasId_1644 (coe v8))
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.CopyFree._.cf-strP
d_cf'45'strP_1056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_cf'45'strP_1056 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
  = du_cf'45'strP_1056 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_cf'45'strP_1056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Bool -> AgdaAny -> AgdaAny
du_cf'45'strP_1056 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v7
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   d_cf'45'strO_1042 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                   (coe v6)
                   (coe
                      du_not'45''8744''691'_856
                      (coe MAlonzo.Code.Once.LinCore.Core.du_hasId_1644 (coe v4))
                      (coe du_coCopies_740 (coe v5)))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_cf'45'strL_980 (coe v4))
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   d_cf'45'strO_1042 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v6) (coe v8))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                   (coe du_cf'45'strL_980 (coe v5))))
-- Once.LinCore.CopyFree._.cf-mapNu
d_cf'45'mapNu_1146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> AgdaAny -> AgdaAny
d_cf'45'mapNu_1146 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_cf'45'mapNu_1146 v4 v6
du_cf'45'mapNu_1146 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> AgdaAny -> AgdaAny
du_cf'45'mapNu_1146 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe du_cf'45'mapNu_1146 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe du_cf'45'mapNu_1146 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_cf'45'mapNu_1146 (coe v2) (coe v1))
             (coe du_cf'45'mapNu_1146 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.CopyFree._.cf-obsT
d_cf'45'obsT_1208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cf'45'obsT_1208 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_cf'45'mapNu_1146 (coe v3) (coe v5))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            d_cf'45'strO_1042 (coe v0) (coe v1) (coe v2) (coe v3) (coe v3)
            (coe v4) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
