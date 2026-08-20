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

module MAlonzo.Code.Once.Adequacy.AnaErased where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Functor.Laws
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.AnaErased.sem-ana-anaS-bisim
d_sem'45'ana'45'anaS'45'bisim_18 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.Laws.T__'8764'S__82
d_sem'45'ana'45'anaS'45'bisim_18 v0 v1 ~v2 v3 v4
  = du_sem'45'ana'45'anaS'45'bisim_18 v0 v1 v3 v4
du_sem'45'ana'45'anaS'45'bisim_18 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.Laws.T__'8764'S__82
du_sem'45'ana'45'anaS'45'bisim_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Semantics.Functor.Laws.C_constructor_94
      (coe
         du_sem'45'ana'45'anaS'45'rel_32 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v1))
         (coe
            MAlonzo.Code.Once.Semantics.Value.du_coerce'45'ν'45'in_982 v1
            erased (coe v2 v3)))
-- Once.Adequacy.AnaErased.sem-ana-anaS-rel
d_sem'45'ana'45'anaS'45'rel_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_sem'45'ana'45'anaS'45'rel_32 v0 v1 ~v2 v3 v4 v5
  = du_sem'45'ana'45'anaS'45'rel_32 v0 v1 v3 v4 v5
du_sem'45'ana'45'anaS'45'rel_32 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
du_sem'45'ana'45'anaS'45'rel_32 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> erased
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             du_sem'45'ana'45'anaS'45'bisim_18 (coe v0) (coe v1) (coe v2)
             (coe v4)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    du_sem'45'ana'45'anaS'45'rel_32 (coe v0) (coe v1) (coe v2) (coe v5)
                    (coe v7)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    du_sem'45'ana'45'anaS'45'rel_32 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sem'45'ana'45'anaS'45'rel_32 (coe v0) (coe v1) (coe v2) (coe v5)
                       (coe v7))
                    (coe
                       du_sem'45'ana'45'anaS'45'rel_32 (coe v0) (coe v1) (coe v2) (coe v6)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AnaErased.sem-ana-anaS
d_sem'45'ana'45'anaS_86 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'anaS_86 = erased
-- Once.Adequacy.AnaErased.anaS-subst-nat
d_anaS'45'subst'45'nat_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'subst'45'nat_106 = erased
-- Once.Adequacy.AnaErased.sem-ana-erase-coh′
d_sem'45'ana'45'erase'45'coh'8242'_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'erase'45'coh'8242'_130 = erased
-- Once.Adequacy.AnaErased.sem-ana-erase-full
d_sem'45'ana'45'erase'45'full_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'erase'45'full_172 = erased
-- Once.Adequacy.AnaErased.SFRel
d_SFRel_190 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_SFRel_190 = erased
-- Once.Adequacy.AnaErased.events-F-erase
d_events'45'F'45'erase_274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (AgdaAny ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'45'F'45'erase_274 = erased
-- Once.Adequacy.AnaErased.TRel
d_TRel_368 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny -> ()
d_TRel_368 = erased
-- Once.Adequacy.AnaErased.coerce-SFRel
d_coerce'45'SFRel_446 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_coerce'45'SFRel_446 ~v0 v1 ~v2 v3 v4 v5
  = du_coerce'45'SFRel_446 v1 v3 v4 v5
du_coerce'45'SFRel_446 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_coerce'45'SFRel_446 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v3
      MAlonzo.Code.Once.Type.C__'8853'__118 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe du_coerce'45'SFRel_446 (coe v4) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe du_coerce'45'SFRel_446 (coe v5) (coe v6) (coe v7) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe du_coerce'45'SFRel_446 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe du_coerce'45'SFRel_446 (coe v5) (coe v7) (coe v9) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AnaErased.push×
d_push'215'_512 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'215'_512 = erased
-- Once.Adequacy.AnaErased.push×⁻
d_push'215''8315'_534 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'215''8315'_534 = erased
-- Once.Adequacy.AnaErased.push⊎₁
d_push'8846''8321'_554 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321'_554 = erased
-- Once.Adequacy.AnaErased.push⊎₁⁻
d_push'8846''8321''8315'_572 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8321''8315'_572 = erased
-- Once.Adequacy.AnaErased.push⊎₂
d_push'8846''8322'_590 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322'_590 = erased
-- Once.Adequacy.AnaErased.push⊎₂⁻
d_push'8846''8322''8315'_608 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8846''8322''8315'_608 = erased
-- Once.Adequacy.AnaErased.push→
d_push'8594'_632 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8594'_632 = erased
-- Once.Adequacy.AnaErased.push→⁻
d_push'8594''8315'_658 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8594''8315'_658 = erased
-- Once.Adequacy.AnaErased.push→Tᵈ
d_push'8594'T'7496'_684 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'8594'T'7496'_684 = erased
-- Once.Adequacy.AnaErased.subst-T-value
d_subst'45'T'45'value_698 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'value_698 = erased
-- Once.Adequacy.AnaErased.subst-T-returnT
d_subst'45'T'45'returnT_710 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'T'45'returnT_710 = erased
-- Once.Adequacy.AnaErased.forget-coh-gen
d_forget'45'coh'45'gen_718 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_forget'45'coh'45'gen_718 = erased
-- Once.Adequacy.AnaErased.inject-coh-nat
d_inject'45'coh'45'nat_724 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inject'45'coh'45'nat_724 = erased
-- Once.Adequacy.AnaErased.pushᴵ+₁
d_push'7477''43''8321'_856 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7477''43''8321'_856 = erased
-- Once.Adequacy.AnaErased.pushᴵ+₂
d_push'7477''43''8322'_874 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7477''43''8322'_874 = erased
-- Once.Adequacy.AnaErased.pushᴵ*
d_push'7477''42'_894 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'7477''42'_894 = erased
-- Once.Adequacy.AnaErased.pushⱽ+₁
d_push'11389''43''8321'_914 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'11389''43''8321'_914 = erased
-- Once.Adequacy.AnaErased.pushⱽ+₂
d_push'11389''43''8322'_932 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'11389''43''8322'_932 = erased
-- Once.Adequacy.AnaErased.pushⱽ*
d_push'11389''42'_952 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'11389''42'_952 = erased
-- Once.Adequacy.AnaErased.ve-split⊕₁
d_ve'45'split'8853''8321'_966 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ve'45'split'8853''8321'_966 = erased
-- Once.Adequacy.AnaErased.ve-split⊕₂
d_ve'45'split'8853''8322'_986 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ve'45'split'8853''8322'_986 = erased
-- Once.Adequacy.AnaErased.ve-split⊗
d_ve'45'split'8855'_1008 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ve'45'split'8855'_1008 = erased
-- Once.Adequacy.AnaErased.coh-to-TRel
d_coh'45'to'45'TRel_1028 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coh'45'to'45'TRel_1028 ~v0 v1 ~v2 v3
  = du_coh'45'to'45'TRel_1028 v1 v3
du_coh'45'to'45'TRel_1028 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coh'45'to'45'TRel_1028 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Id_116 -> erased
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe du_coh'45'to'45'TRel_1028 (coe v2) (coe v4)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe du_coh'45'to'45'TRel_1028 (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coh'45'to'45'TRel_1028 (coe v2) (coe v4))
                    (coe du_coh'45'to'45'TRel_1028 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AnaErased.base-in
d_base'45'in_1072 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'in_1072 = erased
-- Once.Adequacy.AnaErased.pushSK
d_pushSK_1132 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushSK_1132 = erased
-- Once.Adequacy.AnaErased.subst-KF-const
d_subst'45'KF'45'const_1148 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'KF'45'const_1148 = erased
-- Once.Adequacy.AnaErased.VE0
d_VE0_1158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_VE0_1158 ~v0 v1 v2 v3 = du_VE0_1158 v1 v2 v3
du_VE0_1158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_VE0_1158 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
      (coe
         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
         (coe
            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
            (coe MAlonzo.Code.Once.IRTy.d_eraseF_40 (coe v0))
            (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))))
      (coe v2)
-- Once.Adequacy.AnaErased.push-⊎fam₁
d_push'45''8846'fam'8321'_1182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846'fam'8321'_1182 = erased
-- Once.Adequacy.AnaErased.push-⊎fam₂
d_push'45''8846'fam'8322'_1206 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''8846'fam'8322'_1206 = erased
-- Once.Adequacy.AnaErased.push-×fam
d_push'45''215'fam_1232 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_push'45''215'fam_1232 = erased
-- Once.Adequacy.AnaErased.pushS⊕₁
d_pushS'8853''8321'_1262 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8321'_1262 = erased
-- Once.Adequacy.AnaErased.pushS⊕₂
d_pushS'8853''8322'_1286 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8853''8322'_1286 = erased
-- Once.Adequacy.AnaErased.pushS⊗
d_pushS'8855'_1314 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pushS'8855'_1314 = erased
-- Once.Adequacy.AnaErased.vs-split⊕₁
d_vs'45'split'8853''8321'_1328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vs'45'split'8853''8321'_1328 = erased
-- Once.Adequacy.AnaErased.vs-split⊕₂
d_vs'45'split'8853''8322'_1346 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vs'45'split'8853''8322'_1346 = erased
-- Once.Adequacy.AnaErased.vs-split⊗
d_vs'45'split'8855'_1366 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_vs'45'split'8855'_1366 = erased
-- Once.Adequacy.AnaErased.coerce-νin-erase
d_coerce'45'νin'45'erase_1388 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'νin'45'erase_1388 = erased
