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
import qualified MAlonzo.Code.Once.Type

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
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_seqF_28 v0 ~v1 v2 = du_seqF_28 v0 v2
du_seqF_28 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_seqF_28 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v2
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194 v1
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__116 v2 v3
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
      MAlonzo.Code.Once.Type.C__'8855'__118 v2 v3
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
-- Once.Denotation.ValueDomain.anaᵈ-subst-nat
d_ana'7496''45'subst'45'nat_172 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'subst'45'nat_172 = erased
-- Once.Denotation.ValueDomain.anaᵈ-erase
d_ana'7496''45'erase_194 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'erase_194 = erased
-- Once.Denotation.ValueDomain.anaᵈ-erase-full
d_ana'7496''45'erase'45'full_234 ::
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
d_ana'7496''45'erase'45'full_234 = erased
-- Once.Denotation.ValueDomain.subst-νᵈ-cong
d_subst'45'ν'7496''45'cong_256 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ν'7496'_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ν'7496''45'cong_256 = erased
-- Once.Denotation.ValueDomain.anaFᵈ
d_anaF'7496'_264 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
d_anaF'7496'_264 v0 ~v1 v2 = du_anaF'7496'_264 v0 v2
du_anaF'7496'_264 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  AgdaAny -> T_ν'7496'_8
du_anaF'7496'_264 v0 v1
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
d_'10214'_'10215''7472'_274 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7472'_274 = erased
-- Once.Denotation.ValueDomain.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_306 = erased
-- Once.Denotation.ValueDomain.cohᴰ
d_coh'7472'_312 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh'7472'_312 = erased
-- Once.Denotation.ValueDomain.forgetᵇ
d_forget'7495'_356 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_forget'7495'_356 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_forget'7495'_356 (coe v7) (coe v5) (coe v9))
                           (coe d_forget'7495'_356 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_forget'7495'_356 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_forget'7495'_356 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.injectᵇ
d_inject'7495'_386 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_inject'7495'_386 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_inject'7495'_386 (coe v7) (coe v5) (coe v9))
                           (coe d_inject'7495'_386 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe d_inject'7495'_386 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe d_inject'7495'_386 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.coerce-functor-D
d_coerce'45'functor'45'D_418 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'45'D_418 v0 v1 ~v2 v3
  = du_coerce'45'functor'45'D_418 v0 v1 v3
du_coerce'45'functor'45'D_418 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_coerce'45'functor'45'D_418 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe d_forget'7495'_356 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'functor'45'D_418 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'functor'45'D_418 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'functor'45'D_418 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'functor'45'D_418 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.coerce-functor⁻¹-D
d_coerce'45'functor'8315''185''45'D_460 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185''45'D_460 v0 v1 ~v2 v3
  = du_coerce'45'functor'8315''185''45'D_460 v0 v1 v3
du_coerce'45'functor'8315''185''45'D_460 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185''45'D_460 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe d_inject'7495'_386 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'functor'8315''185''45'D_460 (coe v7) (coe v5)
                              (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'functor'8315''185''45'D_460 (coe v8) (coe v6)
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'functor'8315''185''45'D_460 (coe v7) (coe v5)
                              (coe v9))
                           (coe
                              du_coerce'45'functor'8315''185''45'D_460 (coe v8) (coe v6)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
