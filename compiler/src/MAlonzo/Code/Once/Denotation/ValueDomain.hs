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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.ValueDomain.νᵈ
d_ν'7496'_8 a0 = ()
data T_ν'7496'_8
  = C_constructor_16 MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
-- Once.Denotation.ValueDomain.νᵈ.forceᵈ
d_force'7496'_14 ::
  T_ν'7496'_8 -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_force'7496'_14 v0
  = case coe v0 of
      C_constructor_16 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.forgetν
d_forgetν_20 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  T_ν'7496'_8 -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_forgetν_20 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe
         d_forgetLayer_26 (coe v0) (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
            (coe d_force'7496'_14 (coe v1))))
-- Once.Denotation.ValueDomain.forgetLayer
d_forgetLayer_26 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_forgetLayer_26 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v2
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe d_mapForgetν_32 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.mapForgetν
d_mapForgetν_32 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapForgetν_32 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_forgetν_20 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapForgetν_32 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapForgetν_32 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapForgetν_32 (coe v0) (coe v3) (coe v5))
                    (coe d_mapForgetν_32 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.in-νᵈ
d_in'45'ν'7496'_86 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> T_ν'7496'_8
d_in'45'ν'7496'_86 ~v0 v1 = du_in'45'ν'7496'_86 v1
du_in'45'ν'7496'_86 :: AgdaAny -> T_ν'7496'_8
du_in'45'ν'7496'_86 v0
  = coe
      C_constructor_16
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
         (coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe MAlonzo.Code.Once.Res.C_returns_12 (coe v0)))
-- Once.Denotation.ValueDomain.injectν
d_injectν_94 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> T_ν'7496'_8
d_injectν_94 v0 v1
  = coe
      C_constructor_16
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
         (coe (\ v2 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe
            d_injectLayer_100 (coe v0) (coe v0)
            (coe MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v1))))
-- Once.Denotation.ValueDomain.injectLayer
d_injectLayer_100 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_injectLayer_100 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v2
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe d_mapInjectν_106 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.mapInjectν
d_mapInjectν_106 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_mapInjectν_106 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v2
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_injectν_94 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_mapInjectν_106 (coe v0) (coe v3) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_mapInjectν_106 (coe v0) (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_mapInjectν_106 (coe v0) (coe v3) (coe v5))
                    (coe d_mapInjectν_106 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.forgetν-coh
d_forgetν'45'coh_172 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ν'7496'_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forgetν'45'coh_172 = erased
-- Once.Denotation.ValueDomain.injectν-coh
d_injectν'45'coh_188 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_injectν'45'coh_188 = erased
-- Once.Denotation.ValueDomain.seqF
d_seqF_196 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
d_seqF_196 v0 ~v1 v2 = du_seqF_196 v0 v2
du_seqF_196 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10
du_seqF_196 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34 (coe v1)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF_196 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF_196 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
                    (coe du_seqF_196 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
                            (coe du_seqF_196 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.anaᵈ
d_ana'7496'_232 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> T_ν'7496'_8
d_ana'7496'_232 v0 ~v1 v2 v3 = du_ana'7496'_232 v0 v2 v3
du_ana'7496'_232 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> T_ν'7496'_8
du_ana'7496'_232 v0 v1 v2
  = coe
      C_constructor_16
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18 (coe v1 v2) v3))
         (coe
            du_anaLayer_238 (coe v0) (coe v1)
            (coe
               MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20 (coe v1 v2))))
-- Once.Denotation.ValueDomain.anaLayer
d_anaLayer_238 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_anaLayer_238 v0 ~v1 v2 v3 = du_anaLayer_238 v0 v2 v3
du_anaLayer_238 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_anaLayer_238 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v2
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe du_mapAna'7496'_246 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.mapAnaᵈ
d_mapAna'7496'_246 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> AgdaAny
d_mapAna'7496'_246 v0 v1 ~v2 v3 v4
  = du_mapAna'7496'_246 v0 v1 v3 v4
du_mapAna'7496'_246 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> AgdaAny
du_mapAna'7496'_246 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_ana'7496'_232 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7496'_246 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7496'_246 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7496'_246 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7496'_246 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.anaᵈ-subst-nat
d_ana'7496''45'subst'45'nat_326 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'subst'45'nat_326 = erased
-- Once.Denotation.ValueDomain.anaᵈ-erase
d_ana'7496''45'erase_348 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'erase_348 = erased
-- Once.Denotation.ValueDomain.anaᵈ-erase-full
d_ana'7496''45'erase'45'full_388 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'erase'45'full_388 = erased
-- Once.Denotation.ValueDomain.subst-νᵈ-cong
d_subst'45'ν'7496''45'cong_410 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_ν'7496'_8 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ν'7496''45'cong_410 = erased
-- Once.Denotation.ValueDomain.anaFᵈ
d_anaF'7496'_418 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> T_ν'7496'_8
d_anaF'7496'_418 v0 ~v1 v2 = du_anaF'7496'_418 v0 v2
du_anaF'7496'_418 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  AgdaAny -> T_ν'7496'_8
du_anaF'7496'_418 v0 v1
  = coe
      du_ana'7496'_232
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_92
              (coe
                 MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_996 v0
                 erased)
              (coe v1 v2)))
-- Once.Denotation.ValueDomain.⟦_⟧ᴰ
d_'10214'_'10215''7472'_428 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7472'_428 = erased
-- Once.Denotation.ValueDomain.⟦_⟧ᴰᴵ
d_'10214'_'10215''7472''7477'_460 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> ()
d_'10214'_'10215''7472''7477'_460 = erased
-- Once.Denotation.ValueDomain.cohᴰ
d_coh'7472'_466 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coh'7472'_466 = erased
-- Once.Denotation.ValueDomain.forget
d_forget_510 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_forget_510 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_forget_510 (coe v2) (coe v4))
                    (coe d_forget_510 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_forget_510 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_forget_510 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_forget_510 (coe v4))
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20 (coe v1 v7)))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_forget_510 (coe v4))
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                                   (coe v1 (d_inject_514 (coe v2) (coe v7)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_forget_510 (coe v4))
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                                   (coe v1 (d_inject_514 (coe v2) (coe v7)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2 v3
        -> coe
             d_forgetν_20
             (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
             (coe v1)
      MAlonzo.Code.Once.Type.C_Int_132 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_138 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.inject
d_inject_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_inject_514 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_inject_514 (coe v2) (coe v4))
                    (coe d_inject_514 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_inject_514 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_inject_514 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
                                (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_inject_514 (coe v4))
                                   (coe v1 v7)))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
                                (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_inject_514 (coe v4))
                                   (coe v1 (d_forget_510 (coe v2) (coe v7)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.C_mkT_22
                                (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Once.Res.du_mapRes_46 (coe d_inject_514 (coe v4))
                                   (coe v1 (d_forget_510 (coe v2) (coe v7)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2 v3
        -> coe
             d_injectν_94
             (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
             (coe v1)
      MAlonzo.Code.Once.Type.C_Int_132 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_138 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.emit-D
d_emit'45'D_656 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_emit'45'D_656 v0 ~v1 v2 v3 = du_emit'45'D_656 v0 v2 v3
du_emit'45'D_656 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
du_emit'45'D_656 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.SigOp.Info.du_effect'45'of_210
              (coe MAlonzo.Code.Once.SigOp.Info.d_sem_178 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.SigOp.Info.C_Pure_126
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.SigOp.Info.C_Emits_128
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_144 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.SigOp.Info.C_Halts_130
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_144 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.ValueDomain.sig1ᴰ
d_sig1'7472'_678 ::
  Integer ->
  MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120 ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_sig1'7472'_678 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Denotation.ValueDomain.capN
d_capN_682 ::
  Integer ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120] ->
  [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_capN_682 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3 -> coe d_sig1'7472'_678 (coe v0) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.emit-Dᵇ
d_emit'45'D'7495'_696 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_emit'45'D'7495'_696 v0 ~v1 v2 v3 v4
  = du_emit'45'D'7495'_696 v0 v2 v3 v4
du_emit'45'D'7495'_696 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
du_emit'45'D'7495'_696 v0 v1 v2 v3
  = coe
      d_capN_682 (coe v3)
      (coe du_emit'45'D_656 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.ValueDomain.emit-Dᵇ-[]
d_emit'45'D'7495''45''91''93'_714 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_162 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_emit'45'D'7495''45''91''93'_714 = erased
-- Once.Denotation.ValueDomain.coerce-functor-D
d_coerce'45'functor'45'D_728 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'45'D_728 v0 ~v1 v2
  = du_coerce'45'functor'45'D_728 v0 v2
du_coerce'45'functor'45'D_728 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor'45'D_728 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> coe d_forget_510 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'45'D_728 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'45'D_728 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'45'D_728 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'45'D_728 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomain.coerce-functor⁻¹-D
d_coerce'45'functor'8315''185''45'D_770 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185''45'D_770 v0 ~v1 v2
  = du_coerce'45'functor'8315''185''45'D_770 v0 v2
du_coerce'45'functor'8315''185''45'D_770 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185''45'D_770 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> coe d_inject_514 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185''45'D_770 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185''45'D_770 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185''45'D_770 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185''45'D_770 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
