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

module MAlonzo.Code.Once.Adequacy.TeleEntry where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.TeleEntry.φ
d_φ_10 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
d_φ_10 ~v0 v1 = du_φ_10 v1
du_φ_10 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8
du_φ_10 v0
  = coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v0)
-- Once.Adequacy.TeleEntry._.RelGM
d_RelGM_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGM_14 = erased
-- Once.Adequacy.TeleEntry._.RelGT
d_RelGT_16 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 -> ()
d_RelGT_16 = erased
-- Once.Adequacy.TeleEntry._.RelGV
d_RelGV_20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny -> ()
d_RelGV_20 = erased
-- Once.Adequacy.TeleEntry._.abiT
d_abiT_24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_abiT_24 ~v0 ~v1 = du_abiT_24
du_abiT_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
du_abiT_24 = coe MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158
-- Once.Adequacy.TeleEntry.returns-of
d_returns'45'of_34 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_returns'45'of_34 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_returns'45'of_34 v4 v5
du_returns'45'of_34 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_returns'45'of_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEntry.abi-many
d_abi'45'many_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'many_70 = erased
-- Once.Adequacy.TeleEntry.abi-zero
d_abi'45'zero_94 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'zero_94 = erased
-- Once.Adequacy.TeleEntry.abi-rel
d_abi'45'rel_104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_abi'45'rel_104 ~v0 ~v1 v2 ~v3 v4 v5 = du_abi'45'rel_104 v2 v4 v5
du_abi'45'rel_104 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_abi'45'rel_104 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v6 v7
               -> coe
                    seq (coe v6)
                    (let v8 = coe du_returns'45'of_34 (coe v1) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                   -> coe
                                        MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'return_198
                                        (coe v12)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v3 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
