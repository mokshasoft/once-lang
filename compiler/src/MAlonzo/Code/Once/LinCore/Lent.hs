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

module MAlonzo.Code.Once.LinCore.Lent where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.TyEq
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.Lent._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.Lent._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.Lent._.Own
d_Own_90 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.Lent._.Tm
d_Tm_100 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.Lent.Fact
d_Fact_730 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Fact_730 = erased
-- Once.LinCore.Lent.uncond
d_uncond_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uncond_732 ~v0 v1 = du_uncond_732 v1
du_uncond_732 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uncond_732 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v1))
             (coe du_uncond_732 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.under
d_under_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_under_738 ~v0 v1 v2 = du_under_738 v1 v2
du_under_738 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_under_738 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)) (coe v2))
             (coe du_under_738 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.shallow
d_shallow_756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_shallow_756 ~v0 ~v1 v2 v3 v4 v5 = du_shallow_756 v2 v3 v4 v5
du_shallow_756 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_shallow_756 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v6 v9 v10
           -> coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_shallow_756 (coe v0) (coe v6) (coe v2) (coe v9))
                (coe du_shallow_756 (coe v0) (coe v1) (coe v6) (coe v10))
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v10 v11
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe du_shallow_756 (coe v0) (coe v12) (coe v14) (coe v10))
                              (coe du_shallow_756 (coe v0) (coe v13) (coe v15) (coe v11))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_shallow_756 (coe v0) (coe v11) (coe v2) (coe v9))
                       (coe du_shallow_756 (coe v0) (coe v12) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_lend_976 v9
           -> case coe v1 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> case coe v2 of
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v12 v13
                         -> coe
                              du_shallow_756
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v10))
                              (coe v11) (coe v13) (coe v9)
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_blift_984 v8
           -> coe
                du_shallow_756 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                (coe v1) (coe v2) (coe v8)
         MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_shallow_756 (coe v10) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v9
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v10 v11
                  -> coe du_shallow_756 (coe v11) (coe v1) (coe v2) (coe v9)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bcaseE_1014 v9 v10
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
                  -> coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe du_shallow_756 (coe v11) (coe v1) (coe v2) (coe v9))
                       (coe du_shallow_756 (coe v12) (coe v1) (coe v2) (coe v10))
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bout_1022 v8
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                  -> coe
                       du_shallow_756
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9) (coe v0))
                       (coe v1) (coe v2) (coe v8)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_bev_1084
           -> case coe v0 of
                MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                          (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v9) (coe v1)
                          (coe v2))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                _ -> coe v4
         MAlonzo.Code.Once.LinCore.Core.C_liter_1144 v8 v9
           -> coe
                du_shallow_756 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v2) (coe v1))
                (coe v8)
         _ -> coe v4)
-- Once.LinCore.Lent.shallowO
d_shallowO_802 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_shallowO_802 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_shallowO_802 v2 v3 v4 v5 v6
du_shallowO_802 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Own_1880 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_shallowO_802 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.LinCore.Core.C_o'45'bg_1892
        -> coe du_shallow_756 (coe v0) (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_o'45'ev_1900
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fst_1912 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v17
                      -> coe
                           du_shallowO_802 (coe v11) (coe v1) (coe v2) (coe v17) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'snd_1924 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v17
                      -> coe
                           du_shallowO_802 (coe v12) (coe v1) (coe v2) (coe v17) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'split_1940 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v17 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v26
                             -> case coe v21 of
                                  MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v31
                                    -> coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            du_shallowO_802 (coe v14) (coe v17) (coe v2) (coe v26)
                                            (coe v12))
                                         (coe
                                            du_shallowO_802 (coe v15) (coe v1) (coe v17) (coe v31)
                                            (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'case_1954 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898 v19 v20
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              du_shallowO_802 (coe v0) (coe v13) (coe v2) (coe v19) (coe v11))
                           (coe
                              du_shallowO_802 (coe v0) (coe v14) (coe v2) (coe v20) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'fork_1976 v15 v16
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v19 v20
                      -> case coe v3 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v22 v25 v26
                             -> case coe v22 of
                                  MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v27 v28
                                    -> case coe v25 of
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v34 v35
                                           -> case coe v34 of
                                                MAlonzo.Code.Once.LinCore.Core.C_bfst_994 v40
                                                  -> case coe v35 of
                                                       MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004 v45
                                                         -> coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 du_shallowO_802 (coe v17) (coe v27)
                                                                 (coe v19) (coe v40) (coe v15))
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                 (coe
                                                                    du_shallowO_802 (coe v18)
                                                                    (coe v28) (coe v20) (coe v45)
                                                                    (coe v16))
                                                                 (coe
                                                                    du_shallow_756 (coe v0) (coe v1)
                                                                    (coe v22) (coe v26)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'lift_1990 v11
        -> case coe v3 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v13 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.LinCore.Core.C_blift_984 v21
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              du_shallow_756 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                              (coe v13) (coe v2) (coe v21))
                           (coe
                              du_shallowO_802 (coe v0) (coe v1) (coe v13) (coe v17) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_o'45'pre_2004 v11
        -> case coe v3 of
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v13 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.LinCore.Core.C_blift_984 v21
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              du_shallowO_802 (coe v0) (coe v13) (coe v2) (coe v16) (coe v11))
                           (coe
                              du_shallow_756 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                              (coe v1) (coe v13) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.elemT
d_elemT_852 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
d_elemT_852 ~v0 v1 v2 = du_elemT_852 v1 v2
du_elemT_852 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
du_elemT_852 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe MAlonzo.Code.Once.LinCore.TyEq.du_eqT_1106 (coe v0) (coe v2))
             (coe du_elemT_852 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.holds
d_holds_862 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
d_holds_862 ~v0 v1 v2 = du_holds_862 v1 v2
du_holds_862 ::
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
du_holds_862 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe du_elemT_852 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.add
d_add_870 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_add_870 ~v0 v1 v2 v3 = du_add_870 v1 v2 v3
du_add_870 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_add_870 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe du_holds_862 (coe v3) (coe v0))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d_not_22
                   (coe du_elemT_852 (coe v4) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.stepL
d_stepL_880 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_stepL_880 ~v0 v1 v2 = du_stepL_880 v1 v2
du_stepL_880 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_stepL_880 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_add_870 (coe v1) (coe v2) (coe du_stepL_880 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.iter
d_iter_890 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_iter_890 ~v0 v1 v2 v3 = du_iter_890 v1 v2 v3
du_iter_890 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_iter_890 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_iter_890 (coe v3) (coe v1) (coe du_stepL_880 (coe v1) (coe v2)))
-- Once.LinCore.Lent.targets
d_targets_902 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_targets_902 ~v0 v1 = du_targets_902 v1
du_targets_902 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_targets_902 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                    (coe du_targets_902 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.closed?
d_closed'63'_908 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
d_closed'63'_908 ~v0 v1 v2 = du_closed'63'_908 v1 v2
du_closed'63'_908 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Bool
du_closed'63'_908 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d_not_22
                          (coe du_holds_862 (coe v4) (coe v1)))
                       (coe du_elemT_852 (coe v5) (coe v1)))
                    (coe du_closed'63'_908 (coe v3) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Lent.lentTys
d_lentTys_920 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_lentTys_920 ~v0 v1 = du_lentTys_920 v1
du_lentTys_920 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_lentTys_920 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         du_closed'63'_908 (coe v0)
         (coe
            du_iter_890
            (coe
               addInt (coe (1 :: Integer))
               (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
            (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         du_iter_890
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
         (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe du_targets_902 (coe v0))
-- Once.LinCore.Lent.∧-l
d_'8743''45'l_930 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'l_930 = erased
-- Once.LinCore.Lent.∧-r
d_'8743''45'r_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'r_938 = erased
-- Once.LinCore.Lent.∨-r
d_'8744''45'r_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'r_946 = erased
-- Once.LinCore.Lent.∨-l′
d_'8744''45'l'8242'_954 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'l'8242'_954 = erased
-- Once.LinCore.Lent.∨-r′
d_'8744''45'r'8242'_962 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'r'8242'_962 = erased
-- Once.LinCore.Lent.closed-∈
d_closed'45''8712'_976 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closed'45''8712'_976 = erased
-- Once.LinCore.Lent.elem-self
d_elem'45'self_1008 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elem'45'self_1008 = erased
-- Once.LinCore.Lent.targets-∈
d_targets'45''8712'_1020 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_targets'45''8712'_1020 = erased
-- Once.LinCore.Lent.by-check
d_by'45'check_1048 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_by'45'check_1048 = erased
-- Once.LinCore.Lent.lent-closed
d_lent'45'closed_1076 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lent'45'closed_1076 = erased
-- Once.LinCore.Lent._.l
d_l_1088 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_l_1088 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_l_1088 v1
du_l_1088 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
du_l_1088 v0
  = coe
      du_iter_890
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
      (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
