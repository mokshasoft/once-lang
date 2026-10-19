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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Lang.Iterative
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
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 -> ()
d_RelGM_14 = erased
-- Once.Adequacy.TeleEntry._.abiT
d_abiT_20 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_abiT_20 ~v0 ~v1 = du_abiT_20
du_abiT_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
du_abiT_20 = coe MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158
-- Once.Adequacy.TeleEntry._.inv
d_inv_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inv_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
  = du_inv_54 v12 v13
du_inv_54 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inv_54 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v5
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEntry.abi-many
d_abi'45'many_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'many_88 = erased
-- Once.Adequacy.TeleEntry.abi-zero
d_abi'45'zero_112 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'zero_112 = erased
-- Once.Adequacy.TeleEntry.≡ʳ
d_'8801''691'_128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''691'_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8801''691'_128 v9
du_'8801''691'_128 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''691'_128 v0 = coe v0
-- Once.Adequacy.TeleEntry.abi-rel
d_abi'45'rel_138 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_abi'45'rel_138 ~v0 ~v1 v2 ~v3 v4 v5 = du_abi'45'rel_138 v2 v4 v5
du_abi'45'rel_138 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_abi'45'rel_138 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> let v8
                               = coe
                                   du_inv_54
                                   (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v1))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                      (coe v2)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                       -> case coe v12 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                              -> coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                         (coe v13))
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                            (coe v14))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> let v8
                               = coe
                                   du_inv_54
                                   (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v1))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                      (coe v2)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                       -> case coe v12 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                              -> coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         (\ v15 v16 v17 ->
                                                            coe
                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                              (coe v13 v15 v16 v17)))
                                                      (coe
                                                         (\ v15 v16 v17 ->
                                                            coe
                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                              (coe
                                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                                 (coe v14 v15 v16 v17)))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> let v8
                               = coe
                                   du_inv_54
                                   (coe MAlonzo.Code.Once.Lang.Iterative.d_force_64 (coe v1))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
                                      (coe v2)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                       -> case coe v12 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                              -> coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         (\ v15 v16 v17 ->
                                                            coe
                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                              (coe v13 v15 v16 v17)))
                                                      (coe
                                                         (\ v15 v16 v17 ->
                                                            coe
                                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
                                                              (coe
                                                                 MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                                 (coe v14 v15 v16 v17)))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v3 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v3 v4 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v2
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
