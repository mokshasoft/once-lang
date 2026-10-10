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

module MAlonzo.Code.Once.Adequacy.CataBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Adequacy.SeqRel
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataBridge._.RelT
d_RelT_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelT_12 = erased
-- Once.Adequacy.CataBridge._.RelV
d_RelV_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelV_14 = erased
-- Once.Adequacy.CataBridge.base-refl
d_base'45'refl_22 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_base'45'refl_22 ~v0 ~v1 v2 v3 v4 = du_base'45'refl_22 v2 v3 v4
du_base'45'refl_22 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
du_base'45'refl_22 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_base'45'refl_22 (coe v7) (coe v5) (coe v9))
                           (coe du_base'45'refl_22 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_base'45'refl_22 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_base'45'refl_22 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge.cata-bridge
d_cata'45'bridge_70 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_cata'45'bridge_70 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_cata'45'bridge_70 v2 v4 v5 v6 v7 v8
du_cata'45'bridge_70 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_cata'45'bridge_70 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
      (coe
         (\ v6 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe v0) (coe v1) (coe v6)))
              (coe
                 (\ v7 ->
                    coe
                      v2
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                         (coe v0) (coe v1) (coe v7))))))
      (coe
         (\ v6 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
                 (coe
                    MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
                    (coe v0) (coe v1) (coe v6)))
              (coe
                 (\ v7 ->
                    coe
                      v3
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                         (coe v0) (coe v1) (coe v7))))))
      (coe du_algR'45'full_208 (coe v0) (coe v1) (coe v4)) (coe v5)
-- Once.Adequacy.CataBridge._.RelC
d_RelC_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelC_90 = erased
-- Once.Adequacy.CataBridge._.out-rel
d_out'45'rel_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_out'45'rel_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
                 v13
  = du_out'45'rel_100 v9 v10 v11 v12 v13
du_out'45'rel_100 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_out'45'rel_100 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v6 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_out'45'rel_100 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_out'45'rel_100 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_out'45'rel_100 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_out'45'rel_100 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.z-rel
d_z'45'rel_156 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_z'45'rel_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
               v13
  = du_z'45'rel_156 v9 v10 v11 v12 v13
du_z'45'rel_156 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_z'45'rel_156 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v7
               -> coe
                    du_base'45'refl_22 (coe v7) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
                       (coe v7) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_z'45'rel_156 (coe v9) (coe v7) (coe v11) (coe v12) (coe v4)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_z'45'rel_156 (coe v10) (coe v8) (coe v11) (coe v12) (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_z'45'rel_156 (coe v9) (coe v7) (coe v11) (coe v13)
                                            (coe v15))
                                         (coe
                                            du_z'45'rel_156 (coe v10) (coe v8) (coe v12) (coe v14)
                                            (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.algR-full
d_algR'45'full_208 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_algR'45'full_208 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 v7 ~v8 v9 v10 v11
  = du_algR'45'full_208 v2 v4 v7 v9 v10 v11
du_algR'45'full_208 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_algR'45'full_208 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_422
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
            (coe v0) (coe v1) (coe v3)))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
            (coe v0) (coe v1) (coe v4)))
      (coe
         MAlonzo.Code.Once.Adequacy.SeqRel.du_seqF'45'rel_88 (coe v0)
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
            (coe v0) (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_928
            (coe v0) (coe v1) (coe v4))
         (coe
            du_out'45'rel_100 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)))
      (coe
         (\ v6 v7 v8 ->
            coe
              v2
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                 (coe v0) (coe v1) (coe v6))
              (coe
                 MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                 (coe v0) (coe v1) (coe v7))
              (coe
                 du_z'45'rel_156 (coe v0) (coe v1) (coe v6) (coe v7) (coe v8))))
