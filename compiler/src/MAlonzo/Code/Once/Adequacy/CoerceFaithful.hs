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

module MAlonzo.Code.Once.Adequacy.CoerceFaithful where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Sub
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Surface.CoerceIR
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.CoerceFaithful.≡ˡ
d_'8801''737'_54 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_'8801''737'_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8801''737'_54 v9
du_'8801''737'_54 ::
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_'8801''737'_54 v0 = coe v0
-- Once.Adequacy.CoerceFaithful.subst-T-∘
d_subst'45'T'45''8728'_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45''8728'_70 = erased
-- Once.Adequacy.CoerceFaithful.subst-⟦⟧
d_subst'45''10214''10215'_84 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''10214''10215'_84 = erased
-- Once.Adequacy.CoerceFaithful.eval-subst
d_eval'45'subst_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eval'45'subst_102 = erased
-- Once.Adequacy.CoerceFaithful.uip
d_uip_116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uip_116 = erased
-- Once.Adequacy.CoerceFaithful.sym-sym
d_sym'45'sym_124 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'sym_124 = erased
-- Once.Adequacy.CoerceFaithful.subst-arr
d_subst'45'arr_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arr_146 = erased
-- Once.Adequacy.CoerceFaithful.subst-arr₀
d_subst'45'arr'8320'_164 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'arr'8320'_164 = erased
-- Once.Adequacy.CoerceFaithful.subst-pair
d_subst'45'pair_186 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'pair_186 = erased
-- Once.Adequacy.CoerceFaithful.subst-inj₁
d_subst'45'inj'8321'_206 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'inj'8321'_206 = erased
-- Once.Adequacy.CoerceFaithful.subst-inj₂
d_subst'45'inj'8322'_224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'inj'8322'_224 = erased
-- Once.Adequacy.CoerceFaithful.coeIR-rel
d_coeIR'45'rel_238 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coeIR'45'rel_238 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'unit_18
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v7))
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'int_20
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v7))
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'float_22
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v7))
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v22 v23 v24
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                              (coe
                                                 du_arr'8320'_290 (coe v0) (coe v1) (coe v19)
                                                 (coe v24) (coe v15) (coe v5)
                                                 (coe
                                                    (\ v26 ->
                                                       coe
                                                         v6
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                 (coe v25)))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                              (coe
                                                 d_arr'8321'_314 (coe v0) (coe v1) (coe v17)
                                                 (coe v22) (coe v19) (coe v24) (coe v21) (coe v14)
                                                 (coe v15) (coe v5) (coe v6) (coe v25)))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         (\ v25 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                              (coe
                                                 d_arrω_338 (coe v0) (coe v1) (coe v17) (coe v22)
                                                 (coe v19) (coe v24) (coe v21) (coe v14) (coe v15)
                                                 (coe v5) (coe v6) (coe v25)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v15 v16
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                    -> coe
                                         (\ v21 ->
                                            case coe v21 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                -> coe
                                                     MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                           (coe v0) (coe v1) (coe v2) (coe v15)
                                                           (coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__28
                                                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                 (coe v13))
                                                              (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                                                 (coe v13) (coe v15) (coe v11))
                                                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                           (coe v5))
                                                        (coe
                                                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                           (coe
                                                              MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                              (coe v13) (coe v15) (coe v11)
                                                              (coe v19)))
                                                        (coe
                                                           (\ v24 ->
                                                              coe
                                                                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                                   (coe v0) (coe v1) (coe v2)
                                                                   (coe v16)
                                                                   (coe
                                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                         (coe v14))
                                                                      (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                                                         (coe v14) (coe v16)
                                                                         (coe v12))
                                                                      (coe
                                                                         MAlonzo.Code.Once.IR.C_snd_48))
                                                                   (coe v5))
                                                                (coe
                                                                   (\ v25 ->
                                                                      coe
                                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v24) (coe v25))))))
                                                        (coe
                                                           (\ v24 ->
                                                              coe
                                                                MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                      (coe v14) (coe v16) (coe v12)
                                                                      (coe v20)))
                                                                (coe
                                                                   (\ v25 ->
                                                                      coe
                                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v24) (coe v25))))))
                                                        (coe
                                                           du_comp'45'fst_254 (coe v0) (coe v1)
                                                           (coe v13) (coe v15) (coe v11) (coe v17)
                                                           (coe v19) (coe v22))
                                                        (coe
                                                           (\ v24 v25 v26 ->
                                                              coe
                                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                                   (coe v0) (coe v1) (coe v2)
                                                                   (coe v16)
                                                                   (coe
                                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                                         (coe v14))
                                                                      (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                                                         (coe v14) (coe v16)
                                                                         (coe v12))
                                                                      (coe
                                                                         MAlonzo.Code.Once.IR.C_snd_48))
                                                                   (coe v5))
                                                                (coe
                                                                   MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                                      (coe v14) (coe v16) (coe v12)
                                                                      (coe v20)))
                                                                (coe
                                                                   (\ v27 ->
                                                                      coe
                                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v24) (coe v27))))
                                                                (coe
                                                                   (\ v27 ->
                                                                      coe
                                                                        MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v25) (coe v27))))
                                                                (coe
                                                                   du_comp'45'snd_270 (coe v0)
                                                                   (coe v1) (coe v14) (coe v16)
                                                                   (coe v12) (coe v18) (coe v20)
                                                                   (coe v23))
                                                                (coe
                                                                   (\ v27 v28 v29 ->
                                                                      coe
                                                                        MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe v26) (coe v29)))))))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v15 v16
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                             -> case coe v6 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                    -> coe
                                         (\ v19 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                    (coe v0) (coe v1) (coe v13) (coe v15)
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                                       (coe v13) (coe v15) (coe v11))
                                                    (coe v17))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                       (coe v13) (coe v15) (coe v11) (coe v18)))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                    (coe v0) (coe v1) (coe v15) (coe v3)
                                                    (coe MAlonzo.Code.Once.IR.C_inl_54))
                                                 (coe
                                                    (\ v20 ->
                                                       coe
                                                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                         (coe
                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                            (coe v20))))
                                                 (coe
                                                    d_coeIR'45'rel_238 v0 v1 v13 v15 v11 v17 v18
                                                    v19)
                                                 (coe
                                                    (\ v20 v21 v22 ->
                                                       coe
                                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                         (coe v22)))))
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                    -> coe (\ v19 -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                             -> case coe v6 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                                    -> coe (\ v19 -> MAlonzo.RTE.mazUnreachableError)
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                                    -> coe
                                         (\ v19 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                    (coe v0) (coe v1) (coe v14) (coe v16)
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                                       (coe v14) (coe v16) (coe v12))
                                                    (coe v17))
                                                 (coe
                                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                       (coe v14) (coe v16) (coe v12) (coe v18)))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402
                                                    (coe v0) (coe v1) (coe v16) (coe v3)
                                                    (coe MAlonzo.Code.Once.IR.C_inr_60))
                                                 (coe
                                                    (\ v20 ->
                                                       coe
                                                         MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                                         (coe
                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                            (coe v20))))
                                                 (coe
                                                    d_coeIR'45'rel_238 v0 v1 v14 v16 v12 v17 v18
                                                    v19)
                                                 (coe
                                                    (\ v20 v21 v22 ->
                                                       coe
                                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                                         (coe v22)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'μ_62
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v8))
      MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'ν_70 v10
        -> coe
             (\ v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                  (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful.comp-fst
d_comp'45'fst_254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_comp'45'fst_254 v0 v1 v2 v3 ~v4 v5 v6 v7 ~v8 v9
  = du_comp'45'fst_254 v0 v1 v2 v3 v5 v6 v7 v9
du_comp'45'fst_254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_comp'45'fst_254 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe d_coeIR'45'rel_238 v0 v1 v2 v3 v4 v5 v6 v7)
-- Once.Adequacy.CoerceFaithful.comp-snd
d_comp'45'snd_270 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_comp'45'snd_270 v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9
  = du_comp'45'snd_270 v0 v1 v3 v4 v5 v7 v8 v9
du_comp'45'snd_270 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_comp'45'snd_270 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'737'_996
      (coe d_coeIR'45'rel_238 v0 v1 v2 v3 v4 v5 v6 v7)
-- Once.Adequacy.CoerceFaithful.arr₀
d_arr'8320'_290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_arr'8320'_290 v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 v9 v10 v11
  = du_arr'8320'_290 v0 v1 v4 v5 v8 v9 v10 v11
du_arr'8320'_290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_arr'8320'_290 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe v5 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe v6 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32 (coe v2) (coe v3)
            (coe v4)))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe v2) (coe v3) (coe v4) (coe v8))))
      (coe v7)
      (coe
         d_coeIR'45'rel_238 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Adequacy.CoerceFaithful.arr₁
d_arr'8321'_314 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_arr'8321'_314 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Internal.Type.C__'42'__24
                  (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
               (coe du_AB_608 (coe v2) (coe v4) (coe v6))
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'42'__24
                          (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                          (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                             (coe v3) (coe v2) (coe v7))
                          (coe MAlonzo.Code.Once.IR.C_snd_48))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                    (coe
                       (\ v16 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                               (coe v16)))))))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15)))))
      (coe
         v10
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v3) (coe v2) (coe v7) (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32 (coe v4) (coe v5)
            (coe v8)))
      (coe
         (\ v15 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe v4) (coe v5) (coe v8) (coe v15))))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
            (coe
               MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                  (coe v1)
                  (coe
                     MAlonzo.Code.Once.Internal.Type.C__'42'__24
                     (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                  (coe du_AB_608 (coe v2) (coe v4) (coe v6))
                  (coe MAlonzo.Code.Once.IR.C_fst_42)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
               (coe
                  (\ v15 ->
                     coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                          (coe v1)
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'42'__24
                             (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                          (coe v2)
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                             (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                (coe v3) (coe v2) (coe v7))
                             (coe MAlonzo.Code.Once.IR.C_snd_48))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                       (coe
                          (\ v16 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                  (coe v16)))))))
            (coe
               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                  (coe
                     MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                     (coe v3) (coe v2) (coe v7) (coe v13))))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15))))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15))))
            (coe
               MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
               (coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Internal.Type.C__'42'__24
                        (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                     (coe du_AB_608 (coe v2) (coe v4) (coe v6))
                     (coe MAlonzo.Code.Once.IR.C_fst_42)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                  (coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
                  (coe
                     (\ v15 ->
                        coe
                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                          (coe
                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                             (coe v1)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                             (coe v2)
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                   (coe v3) (coe v2) (coe v7))
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                          (coe
                             (\ v16 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v16))))))
                  (coe
                     (\ v15 ->
                        coe
                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                          (coe
                             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                             (coe
                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                (coe v3) (coe v2) (coe v7) (coe v13)))
                          (coe
                             (\ v16 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v16))))))
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe v11))
                  (coe
                     (\ v15 v16 v17 ->
                        coe
                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                          (coe
                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                             (coe v1)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe du_AB_608 (coe v2) (coe v4) (coe v6)) (coe v3))
                             (coe v2)
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                   (coe v3) (coe v2) (coe v7))
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                          (coe
                             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                             (coe
                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                (coe v3) (coe v2) (coe v7) (coe v13)))
                          (coe
                             (\ v18 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v18))))
                          (coe
                             (\ v18 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                     (coe v18))))
                          (coe
                             du_comp'45'snd_270 (coe v0) (coe v1) (coe v3) (coe v2) (coe v7)
                             (coe v12) (coe v13) (coe v14))
                          (coe
                             (\ v18 v19 v20 ->
                                coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                     (coe v20))))))))
            (coe
               (\ v15 v16 v17 ->
                  case coe v15 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                      -> case coe v16 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                    -> coe v22 v19 v21 v23
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError))))
      (coe
         d_coeIR'45'rel_238 (coe v0) (coe v1) (coe v4) (coe v5) (coe v8))
-- Once.Adequacy.CoerceFaithful.arrω
d_arrω_338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_arrω_338 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
         (coe
            MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
               (coe v1)
               (coe
                  MAlonzo.Code.Once.Internal.Type.C__'42'__24
                  (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
               (coe du_AB_674 (coe v2) (coe v4) (coe v6))
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                       (coe v1)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'42'__24
                          (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                       (coe v2)
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                          (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                             (coe v3) (coe v2) (coe v7))
                          (coe MAlonzo.Code.Once.IR.C_snd_48))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                    (coe
                       (\ v16 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                               (coe v16)))))))
         (coe
            (\ v15 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15)))))
      (coe
         v10
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v3) (coe v2) (coe v7) (coe v13)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
         (coe v1) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32 (coe v4) (coe v5)
            (coe v8)))
      (coe
         (\ v15 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
              (coe
                 MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                 (coe v4) (coe v5) (coe v8) (coe v15))))
      (coe
         MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
            (coe
               MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
               (coe
                  MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                  (coe v1)
                  (coe
                     MAlonzo.Code.Once.Internal.Type.C__'42'__24
                     (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                  (coe du_AB_674 (coe v2) (coe v4) (coe v6))
                  (coe MAlonzo.Code.Once.IR.C_fst_42)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
               (coe
                  (\ v15 ->
                     coe
                       MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                          (coe v1)
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'42'__24
                             (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                          (coe v2)
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                             (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                (coe v3) (coe v2) (coe v7))
                             (coe MAlonzo.Code.Once.IR.C_snd_48))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                       (coe
                          (\ v16 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                  (coe v16)))))))
            (coe
               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                  (coe
                     MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                     (coe v3) (coe v2) (coe v7) (coe v13))))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15))))
            (coe
               (\ v15 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15))))
            (coe
               MAlonzo.Code.Once.Denotation.ValueRel.du_retarget'691'_1016
               (coe
                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Internal.Type.C__'42'__24
                        (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                     (coe du_AB_674 (coe v2) (coe v4) (coe v6))
                     (coe MAlonzo.Code.Once.IR.C_fst_42)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                  (coe
                     MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v10))
                  (coe
                     (\ v15 ->
                        coe
                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                          (coe
                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                             (coe v1)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                             (coe v2)
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                   (coe v3) (coe v2) (coe v7))
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                          (coe
                             (\ v16 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v16))))))
                  (coe
                     (\ v15 ->
                        coe
                          MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                          (coe
                             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                             (coe
                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                (coe v3) (coe v2) (coe v7) (coe v13)))
                          (coe
                             (\ v16 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v16))))))
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                     (coe v11))
                  (coe
                     (\ v15 v16 v17 ->
                        coe
                          MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                          (coe
                             MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                             (coe v1)
                             (coe
                                MAlonzo.Code.Once.Internal.Type.C__'42'__24
                                (coe du_AB_674 (coe v2) (coe v4) (coe v6)) (coe v3))
                             (coe v2)
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                (MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32
                                   (coe v3) (coe v2) (coe v7))
                                (coe MAlonzo.Code.Once.IR.C_snd_48))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v12)))
                          (coe
                             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                             (coe
                                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                (coe v3) (coe v2) (coe v7) (coe v13)))
                          (coe
                             (\ v18 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                     (coe v18))))
                          (coe
                             (\ v18 ->
                                coe
                                  MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                     (coe v18))))
                          (coe
                             du_comp'45'snd_270 (coe v0) (coe v1) (coe v3) (coe v2) (coe v7)
                             (coe v12) (coe v13) (coe v14))
                          (coe
                             (\ v18 v19 v20 ->
                                coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_relS'45'ret_442
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                     (coe v20))))))))
            (coe
               (\ v15 v16 v17 ->
                  case coe v15 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                      -> case coe v16 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                             -> case coe v17 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                    -> coe v22 v19 v21 v23
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError))))
      (coe
         d_coeIR'45'rel_238 (coe v0) (coe v1) (coe v4) (coe v5) (coe v8))
-- Once.Adequacy.CoerceFaithful._.AB
d_AB_608 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_AB_608 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_AB_608 v2 v4 v6
du_AB_608 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_AB_608 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_One_10) (coe v2))
      (coe v1)
-- Once.Adequacy.CoerceFaithful._.AB
d_AB_674 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_AB_674 ~v0 ~v1 v2 ~v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_AB_674 v2 v4 v6
du_AB_674 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_AB_674 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2))
      (coe v1)
-- Once.Adequacy.CoerceFaithful.VfSem
d_VfSem_716 a0 a1 a2 a3 a4 = ()
newtype T_VfSem_716
  = C_constructor_740 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Once.Adequacy.CoerceFaithful.VfSem.D
d_D_732 ::
  T_VfSem_716 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_D_732 = erased
-- Once.Adequacy.CoerceFaithful.VfSem.pt
d_pt_738 :: T_VfSem_716 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_pt_738 v0
  = case coe v0 of
      C_constructor_740 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful.≡ʳᴰ
d_'8801''691''7472'_750 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8801''691''7472'_750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8801''691''7472'_750 v7
du_'8801''691''7472'_750 :: AgdaAny -> AgdaAny
du_'8801''691''7472'_750 v0 = coe v0
-- Once.Adequacy.CoerceFaithful.vf-arr₁
d_vf'45'arr'8321'_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  T_VfSem_716 ->
  T_VfSem_716 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_vf'45'arr'8321'_788 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                      v13 v14 v15
  = du_vf'45'arr'8321'_788
      v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
du_vf'45'arr'8321'_788 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  T_VfSem_716 ->
  T_VfSem_716 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_vf'45'arr'8321'_788 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'691'_622
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v2) (coe v3) (coe v5))
      (coe v8 v11)
      (coe
         v9
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v1) (coe v0) (coe v4) (coe v12)))
      (coe
         v10 v11
         (MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
            (coe v1) (coe v0) (coe v4) (coe v12))
         (coe d_pt_738 v6 v11 v12 v13))
      (coe d_pt_738 (coe v7))
-- Once.Adequacy.CoerceFaithful.vf-sem
d_vf'45'sem_814 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 -> T_VfSem_716
d_vf'45'sem_814 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'void_60
        -> coe
             C_constructor_740 (\ v6 v7 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'unit_62
        -> coe C_constructor_740 (\ v6 v7 v8 -> v8)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'int_64
        -> coe C_constructor_740 (\ v6 v7 v8 -> v8)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'float_66
        -> coe C_constructor_740 (\ v6 v7 v8 -> v8)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'arr_88 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                      -> case coe v3 of
                           MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v23 v24 v25
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'arr_38 v33 v34 v35
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                           -> coe
                                                C_constructor_740
                                                (\ v36 v37 v38 ->
                                                   coe
                                                     MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'691'_622
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                                        (coe v20) (coe v25) (coe v34))
                                                     (coe
                                                        v36
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                     (coe
                                                        v37
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                     (coe v38)
                                                     (coe
                                                        d_pt_738
                                                        (coe
                                                           d_vf'45'sem_814 (coe v0) (coe v1)
                                                           (coe v20) (coe v25) (coe v34)
                                                           (coe v17))))
                                         MAlonzo.Code.Once.Spec.Grade.C_One_10
                                           -> coe
                                                C_constructor_740
                                                (coe
                                                   du_vf'45'arr'8321'_788 (coe v18) (coe v23)
                                                   (coe v20) (coe v25) (coe v33) (coe v34)
                                                   (coe
                                                      d_vf'45'sem_814 (coe v0) (coe v1) (coe v23)
                                                      (coe v18) (coe v33) (coe v16))
                                                   (coe
                                                      d_vf'45'sem_814 (coe v0) (coe v1) (coe v20)
                                                      (coe v25) (coe v34) (coe v17)))
                                         MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                           -> coe
                                                C_constructor_740
                                                (coe
                                                   du_vf'45'arr'8321'_788 (coe v18) (coe v23)
                                                   (coe v20) (coe v25) (coe v33) (coe v34)
                                                   (coe
                                                      d_vf'45'sem_814 (coe v0) (coe v1) (coe v23)
                                                      (coe v18) (coe v33) (coe v16))
                                                   (coe
                                                      d_vf'45'sem_814 (coe v0) (coe v1) (coe v20)
                                                      (coe v25) (coe v34) (coe v17)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'prod_102 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'42'__24 v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v16 v17
                      -> case coe v4 of
                           MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'prod_48 v22 v23
                             -> coe
                                  C_constructor_740
                                  (d_'46'extendedlambda2_894
                                     (coe v0) (coe v1) (coe v14) (coe v16) (coe v15) (coe v17)
                                     (coe v22) (coe v23) (coe v12) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'sum_116 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Type.C__'43'__26 v14 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v16 v17
                      -> case coe v4 of
                           MAlonzo.Code.Once.Internal.Type.Sub.C_sub'45'sum_58 v22 v23
                             -> coe
                                  C_constructor_740
                                  (d_'46'extendedlambda2_924
                                     (coe v0) (coe v1) (coe v14) (coe v16) (coe v15) (coe v17)
                                     (coe v22) (coe v23) (coe v12) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'μ_120
        -> coe C_constructor_740 (\ v7 v8 v9 -> v9)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'ν_130
        -> coe C_constructor_740 (\ v10 v11 v12 -> v12)
      MAlonzo.Code.Once.Surface.CoerceIR.C_vf'45'rigid_136
        -> coe
             C_constructor_740 (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful..extendedlambda2
d_'46'extendedlambda2_894 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'46'extendedlambda2_894 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
               -> case coe v12 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              d_pt_738
                              (d_vf'45'sem_814
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v8))
                              v13 v15 v17)
                           (coe
                              d_pt_738
                              (d_vf'45'sem_814
                                 (coe v0) (coe v1) (coe v4) (coe v5) (coe v7) (coe v9))
                              v14 v16 v18)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful..extendedlambda2
d_'46'extendedlambda2_924 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
d_'46'extendedlambda2_924 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
        -> case coe v11 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
               -> coe
                    d_pt_738
                    (d_vf'45'sem_814
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v8))
                    v13 v14 v12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
        -> case coe v11 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
               -> coe
                    d_pt_738
                    (d_vf'45'sem_814
                       (coe v0) (coe v1) (coe v4) (coe v5) (coe v7) (coe v9))
                    v13 v14 v12
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful.coerce-lift-yes
d_coerce'45'lift'45'yes_954 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'lift'45'yes_954 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.du_RelS'45'fmap'691'_622
      (coe
         MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
         (coe v3) (coe v4) (coe v5))
      (coe
         du_m_982 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
      (coe v9) (coe v10)
      (coe
         d_pt_738
         (coe
            du_s_978 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)))
-- Once.Adequacy.CoerceFaithful._.E
d_E_976 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_976 = erased
-- Once.Adequacy.CoerceFaithful._.s
d_s_978 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  T_VfSem_716
d_s_978 v0 v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_s_978 v0 v1 v3 v4 v5 v6
du_s_978 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 -> T_VfSem_716
du_s_978 v0 v1 v2 v3 v4 v5
  = coe
      d_vf'45'sem_814 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
-- Once.Adequacy.CoerceFaithful._.x₀
d_x'8320'_980 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  AgdaAny
d_x'8320'_980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_x'8320'_980 v8
du_x'8320'_980 :: AgdaAny -> AgdaAny
du_x'8320'_980 v0 = coe v0
-- Once.Adequacy.CoerceFaithful._.m
d_m_982 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.Surface.CoerceIR.T_VoidFree_58 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_m_982 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 v8 ~v9 ~v10
  = du_m_982 v0 v1 v2 v3 v7 v8
du_m_982 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_m_982 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
      (coe v1) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)) (coe v4)
      (coe v5)
-- Once.Adequacy.CoerceFaithful.coerce-lift-dec
d_coerce'45'lift'45'dec_1002 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'lift'45'dec_1002 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then case coe v12 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                      -> coe
                           d_coerce'45'lift'45'yes_954 (coe v0) (coe v1) (coe v2) (coe v3)
                           (coe v4) (coe v5) (coe v13) (coe v7) (coe v8) (coe v9) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v12)
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.du_RelS'45'bind_470
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                          (coe v1) (coe v2) (coe v3) (coe v7) (coe v8))
                       (coe v9)
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_402 (coe v0)
                          (coe v1) (coe v3) (coe v4)
                          (coe
                             MAlonzo.Code.Once.Surface.CoerceIR.d_coeIR_32 (coe v3) (coe v4)
                             (coe v5)))
                       (coe
                          (\ v13 ->
                             coe
                               MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                               (coe
                                  MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                                  (coe v3) (coe v4) (coe v5) (coe v13))))
                       (coe v10)
                       (coe
                          d_coeIR'45'rel_238 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoerceFaithful.coerce-lift
d_coerce'45'lift_1044 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_coerce'45'lift_1044 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_coerce'45'lift'45'dec_1002 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.Surface.CoerceIR.d_voidFree'63'_294 (coe v3)
         (coe v4) (coe v5))
      (coe v6) (coe v7) (coe v8)
