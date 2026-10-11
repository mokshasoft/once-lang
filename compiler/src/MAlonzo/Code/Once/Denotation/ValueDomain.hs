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

module MAlonzo.Code.Once.Denotation.ValueDomain where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed

-- Once.Denotation.ValueDomain.νᵈ
d_ν'7496'_8 a0 = ()
data T_ν'7496'_8
  = C_constructor_16 MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
-- Once.Denotation.ValueDomain.νᵈ.forceᵈ
d_force'7496'_14 ::
  T_ν'7496'_8 -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_force'7496'_14 v0
  = case coe v0 of
      C_constructor_16 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.in-νᵈ
d_in'45'ν'7496'_20 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> T_ν'7496'_8
d_in'45'ν'7496'_20 ~v0 v1 = du_in'45'ν'7496'_20 v1
du_in'45'ν'7496'_20 :: AgdaAny -> T_ν'7496'_8
du_in'45'ν'7496'_20 v0
  = coe
      C_constructor_16
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 (coe v0))
-- Once.Denotation.ValueDomain.seqF
d_seqF_28 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_seqF_28 v0 ~v1 v2 = du_seqF_28 v0 v2
du_seqF_28 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_seqF_28 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_12 v2
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v1
      MAlonzo.Code.Once.Spec.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF_28 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF_28 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe du_seqF_28 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                            (coe du_seqF_28 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.anaᵈ
d_ana'7496'_64 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
d_ana'7496'_64 v0 ~v1 v2 v3 = du_ana'7496'_64 v0 v2 v3
du_ana'7496'_64 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
du_ana'7496'_64 v0 v1 v2
  = coe
      C_constructor_16 (coe du_anaTree_70 (coe v0) (coe v1) (coe v1 v2))
-- Once.Denotation.ValueDomain.anaTree
d_anaTree_70 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_anaTree_70 v0 ~v1 v2 v3 = du_anaTree_70 v0 v2 v3
du_anaTree_70 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_anaTree_70 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v3
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182
             (coe du_mapAna'7496'_78 (coe v0) (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 (coe v3)
             (coe v4)
             (coe (\ v6 -> coe du_anaTree_70 (coe v0) (coe v1) (coe v5 v6)))
      MAlonzo.Code.Once.Denotation.TraceMonad.C_halt_190 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.mapAnaᵈ
d_mapAna'7496'_78 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> AgdaAny
d_mapAna'7496'_78 v0 v1 ~v2 v3 v4 = du_mapAna'7496'_78 v0 v1 v3 v4
du_mapAna'7496'_78 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> AgdaAny
du_mapAna'7496'_78 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_ana'7496'_64 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7496'_78 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7496'_78 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7496'_78 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7496'_78 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.anaᵈ-erase
d_ana'7496''45'erase_174 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'erase_174 = erased
-- Once.Denotation.ValueDomain.anaᵈ-erase-full
d_ana'7496''45'erase'45'full_214 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'erase'45'full_214 = erased
-- Once.Denotation.ValueDomain.subst-νᵈ-cong
d_subst'45'ν'7496''45'cong_236 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ν'7496'_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ν'7496''45'cong_236 = erased
-- Once.Denotation.ValueDomain.anaFᵈ
d_anaF'7496'_244 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
d_anaF'7496'_244 v0 ~v1 v2 = du_anaF'7496'_244 v0 v2
du_anaF'7496'_244 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
du_anaF'7496'_244 v0 v1
  = coe
      du_ana'7496'_64
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
              (coe
                 MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_1120 v0
                 erased)
              (coe v1 v2)))
-- Once.Denotation.ValueDomain.⟦_⟧ᴰ
d_'10214'_'10215''7472'_254 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_'10214'_'10215''7472'_254 = erased
-- Once.Denotation.ValueDomain.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_286 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_286 = erased
-- Once.Denotation.ValueDomain.cohᴰ
d_coh'7472'_292 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh'7472'_292 = erased
-- Once.Denotation.ValueDomain.forgetᵇ
d_forget'7495'_336 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_forget'7495'_336 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_forget'7495'_336 (coe v7) (coe v5) (coe v9))
                           (coe d_forget'7495'_336 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_forget'7495'_336 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_forget'7495'_336 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.injectᵇ
d_inject'7495'_366 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_inject'7495'_366 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Unit_10 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Int_14 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Float_16 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Prod_22 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__24 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_inject'7495'_366 (coe v7) (coe v5) (coe v9))
                           (coe d_inject'7495'_366 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_base'45'Sum_28 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__26 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_inject'7495'_366 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_inject'7495'_366 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.coerce-functor-D
d_coerce'45'functor'45'D_398 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'45'D_398 v0 v1 ~v2 v3
  = du_coerce'45'functor'45'D_398 v0 v1 v3
du_coerce'45'functor'45'D_398 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_coerce'45'functor'45'D_398 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v5
               -> coe d_forget'7495'_336 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'functor'45'D_398 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'functor'45'D_398 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'functor'45'D_398 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'functor'45'D_398 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.coerce-functor⁻¹-D
d_coerce'45'functor'8315''185''45'D_440 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185''45'D_440 v0 v1 ~v2 v3
  = du_coerce'45'functor'8315''185''45'D_440 v0 v1 v3
du_coerce'45'functor'8315''185''45'D_440 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185''45'D_440 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'K_52 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_K_12 v5
               -> coe d_inject'7495'_366 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Id_54 -> coe v2
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Sum_60 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__16 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'functor'8315''185''45'D_440 (coe v7) (coe v5)
                              (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'functor'8315''185''45'D_440 (coe v8) (coe v6)
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.WellFormed.C_wf'45'Prod_66 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__18 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'functor'8315''185''45'D_440 (coe v7) (coe v5)
                              (coe v9))
                           (coe
                              du_coerce'45'functor'8315''185''45'D_440 (coe v8) (coe v6)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
