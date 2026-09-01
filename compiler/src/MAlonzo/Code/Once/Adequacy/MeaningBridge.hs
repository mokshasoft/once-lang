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

module MAlonzo.Code.Once.Adequacy.MeaningBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataBridge
import qualified MAlonzo.Code.Once.Adequacy.InErased
import qualified MAlonzo.Code.Once.Adequacy.MeaningRelation
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.MeaningBridge._.In-ir
d_In'45'ir_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_In'45'ir_10 ~v0 = du_In'45'ir_10
du_In'45'ir_10 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_In'45'ir_10
  = coe MAlonzo.Code.Once.Adequacy.InErased.du_In'45'ir_60
-- Once.Adequacy.MeaningBridge._.RelT
d_RelT_50 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelT_50 = erased
-- Once.Adequacy.MeaningBridge._.RelV
d_RelV_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelV_56 = erased
-- Once.Adequacy.MeaningBridge.subst-∘-move
d_subst'45''8728''45'move_80 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8728''45'move_80 = erased
-- Once.Adequacy.MeaningBridge.RelEnv
d_RelEnv_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  AgdaAny -> AgdaAny -> ()
d_RelEnv_90 = erased
-- Once.Adequacy.MeaningBridge.rel-lookup
d_rel'45'lookup_116 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rel'45'lookup_116 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_rel'45'lookup_116 v2 v3 v4 v5 v6
du_rel'45'lookup_116 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_rel'45'lookup_116 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    seq (coe v2)
                    (coe
                       seq (coe v3)
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError))
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         du_rel'45'lookup_116 (coe v6) (coe v10) (coe v11) (coe v13)
                                         (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.base-rel→eq
d_base'45'rel'8594'eq_160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'rel'8594'eq_160 = erased
-- Once.Adequacy.MeaningBridge.wfF-layer-eq
d_wfF'45'layer'45'eq_234 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wfF'45'layer'45'eq_234 = erased
-- Once.Adequacy.MeaningBridge.base-rel→refl
d_base'45'rel'8594'refl_312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_base'45'rel'8594'refl_312 ~v0 v1 v2 v3
  = du_base'45'rel'8594'refl_312 v1 v2 v3
du_base'45'rel'8594'refl_312 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
du_base'45'rel'8594'refl_312 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_base'45'rel'8594'refl_312 (coe v7) (coe v5) (coe v9))
                           (coe du_base'45'rel'8594'refl_312 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_base'45'rel'8594'refl_312 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_base'45'rel'8594'refl_312 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.concrete-rel→refl
d_concrete'45'rel'8594'refl_350 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> AgdaAny
d_concrete'45'rel'8594'refl_350 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5
        -> coe du_base'45'rel'8594'refl_312 (coe v1) (coe v5) (coe v3)
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> coe
                    (\ v12 v13 v14 ->
                       d_RelT'45'refl_358 (coe v0) (coe v11) (coe v8) (coe v3 v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.RelT-refl
d_RelT'45'refl_358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RelT'45'refl_358 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         d_concrete'45'rel'8594'refl_350 (coe v0) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70 (coe v3)
            (coe v4)))
-- Once.Adequacy.MeaningBridge.sigop-bridge
d_sigop'45'bridge_400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'bridge_400 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_sigop'45'bridge_400 v0 v1 v2 v3 v4 v5 v6 v9
du_sigop'45'bridge_400 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'bridge_400 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         d_concrete'45'rel'8594'refl_350 (coe v0) (coe v2) (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (\ v8 ->
               coe
                 MAlonzo.Code.Once.Denotation.Meaning.du_named'45'sem_60 (coe v1)
                 (coe v2) (coe v0) (coe v3) (coe v4) (coe v5) (coe v6))
            (coe v7)))
-- Once.Adequacy.MeaningBridge.sd-sigOp-base≡
d_sd'45'sigOp'45'base'8801'_438 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'sigOp'45'base'8801'_438 = erased
-- Once.Adequacy.MeaningBridge.sigop-ref-bridge
d_sigop'45'ref'45'bridge_492 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'ref'45'bridge_492 v0 ~v1 ~v2 v3 v4 v5 ~v6
  = du_sigop'45'ref'45'bridge_492 v0 v3 v4 v5
du_sigop'45'ref'45'bridge_492 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'ref'45'bridge_492 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5
        -> coe
             d_RelT'45'refl_358 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5)
             (coe
                MAlonzo.Code.Once.Denotation.Meaning.d_sigOpRef'7472'_136 (coe v1)
                (coe v0) (coe v2)
                (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5))
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8
        -> coe
             d_RelT'45'refl_358 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8)
             (coe
                MAlonzo.Code.Once.Denotation.Meaning.d_sigOpRef'7472'_136 (coe v1)
                (coe v0) (coe v2)
                (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.in-app-bridge
d_in'45'app'45'bridge_526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'app'45'bridge_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_in'45'app'45'bridge_526
du_in'45'app'45'bridge_526 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_in'45'app'45'bridge_526
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.MeaningBridge.sd-fold-is-cata-sem
d_sd'45'fold'45'is'45'cata'45'sem_552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'fold'45'is'45'cata'45'sem_552 = erased
-- Once.Adequacy.MeaningBridge.copair-rel
d_copair'45'rel_586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_copair'45'rel_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
                    v12
  = du_copair'45'rel_586 v8 v9 v10 v11 v12
du_copair'45'rel_586 ::
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_copair'45'rel_586 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v0 v5 v6 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6 -> coe v1 v5 v6 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.≡→RelV-⊎⊤
d_'8801''8594'RelV'45''8846''8868'_612 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8801''8594'RelV'45''8846''8868'_612 ~v0 v1 ~v2 ~v3
  = du_'8801''8594'RelV'45''8846''8868'_612 v1
du_'8801''8594'RelV'45''8846''8868'_612 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8801''8594'RelV'45''8846''8868'_612 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.MeaningBridge.SD-subst-usage
d_SD'45'subst'45'usage_632 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_SD'45'subst'45'usage_632 = erased
-- Once.Adequacy.MeaningBridge.bridge-i
d_bridge'45'i_650 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'i_650 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
        -> coe
             (\ v10 v11 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
        -> coe
             (\ v13 v14 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
        -> coe
             (\ v10 v11 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
        -> coe
             (\ v9 v10 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
        -> coe
             (\ v9 v10 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v12
        -> case coe v12 of
             MAlonzo.Code.Once.Surface.Context.C_svar_218 v17
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368 v18 v19 v20 v21 v22 v23 v24
                      -> coe
                           (\ v25 v26 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_rel'45'lookup_116 (coe v20) (coe v17) (coe v6) (coe v7)
                                   (coe v25)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v13
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         du_sigop'45'ref'45'bridge_492 (coe v0) (coe v3)
                         (coe
                            MAlonzo.Code.Once.CanonicalName.d_bare_12
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20 v15
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("." :: Data.Text.Text) v14)))
                         (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v12
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v13
               -> coe
                    (\ v14 ->
                       coe
                         du_sigop'45'ref'45'bridge_492 (coe v0) (coe v3) (coe v13)
                         (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v14
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
               -> coe
                    (\ v16 ->
                       coe
                         du_sigop'45'ref'45'bridge_492 (coe v0) (coe v3)
                         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v15))
                         (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v11 v12 v13 v14 v20 v22
        -> coe
             (\ v23 v24 ->
                coe
                  d_bridge'45'c_668 v0
                  (MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v1))
                     (coe v13))
                  v12 v3
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v1))
                           (coe v13))))
                  v22 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v24)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v12
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v13 v14
               -> coe
                    (\ v15 ->
                       d_bridge'45'c_668
                         (coe v0) (coe v1) (coe v13) (coe v3) (coe v4) (coe v12) (coe v6)
                         (coe v7) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v13 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v17 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v19 v20
                      -> coe
                           (\ v21 v22 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'i_650 v0 v1 v17 v19 v13 v15 v6 v7 v21 v22))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'i_650 v0 v1 v18 v20 v14 v16 v6 v7 v21 v22))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v11
        -> coe
             (\ v12 v13 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
        -> coe
             (\ v13 v14 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v12 v14 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v19 v20 v21
               -> coe
                    (\ v22 v23 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_bridge'45'i_650 v0
                               (MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                  (coe v1) (coe v19) (coe v12))
                               v21 v3
                               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v16) v18
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                        v1 v20 v12 v15 v17 v0 v6)
                                     (coe v23)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v1))
                                        (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v1) (coe v20) (coe v12) (coe v15) (coe v17))
                                        (coe v0) (coe v7))
                                     (coe v23)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v22)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe d_bridge'45'i_650 v0 v1 v20 v12 v15 v17 v6 v7 v22 v23)))
                               v23)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v14 v15 v17 v18 v19 v20 v21 v22 v23 v24
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v25 v26 v27 v28 v29
               -> coe
                    (\ v30 v31 ->
                       let v32
                             = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                    v1 v25
                                    (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v14) (coe v15))
                                    v19 v22 v0 v6 v31) in
                       coe
                         (let v33
                                = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                       (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                          (coe v1))
                                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v14) (coe v15))
                                       (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                          (coe v1) (coe v25)
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'43'__124 (coe v14)
                                             (coe v15))
                                          (coe v19) (coe v22))
                                       v0 v7 v31) in
                          coe
                            (let v34
                                   = coe
                                       d_bridge'45'i_650 v0 v1 v25
                                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v14) (coe v15))
                                       v19 v22 v6 v7 v30 v31 in
                             coe
                               (case coe v32 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v35
                                    -> case coe v33 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v36
                                           -> case coe v34 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             d_bridge'45'i_650 v0
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                      (coe v1)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                                      (coe v26) (coe v14)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                                      (coe v1)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                                   (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                      (coe v1))
                                                                   v14
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366
                                                                   (coe v1)))
                                                             v27 v3
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                                v17 v20)
                                                             v23
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v6) (coe v35))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v7) (coe v36))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v30) (coe v38))
                                                             v31))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v35
                                    -> case coe v33 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v36
                                           -> case coe v34 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             d_bridge'45'i_650 v0
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                      (coe v1)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                                      (coe v28) (coe v15)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                                      (coe v1)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                                   (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                      (coe v1))
                                                                   v15
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366
                                                                   (coe v1)))
                                                             v29 v3
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                                v18 v21)
                                                             v24
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v6) (coe v35))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v7) (coe v36))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v30) (coe v38))
                                                             v31))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v17 v18 v19
               -> coe
                    seq (coe v17)
                    (coe
                       (\ v20 v21 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v17 v18 v19
               -> coe
                    seq (coe v17)
                    (coe
                       (\ v20 v21 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v17 v18 v19
               -> coe
                    seq (coe v17)
                    (coe
                       (\ v20 v21 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v17 v18 v19
               -> coe
                    seq (coe v17)
                    (coe
                       (\ v20 v21 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v12 v13 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_396 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_398 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_400 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_402 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_404 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_612
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_406 v0
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v18 (coe MAlonzo.Code.Once.Type.C_Int_132) v12 v15
                                               v0 v6)
                                            (coe v21))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                               v1 v19 (coe MAlonzo.Code.Once.Type.C_Int_132) v13 v16
                                               v0 v6)
                                            (coe v21))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 v16 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_bridge'45'i_650 v0 v1 v14 v3 v11 v12 v6 v7 v15 v16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v11 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    (\ v16 v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_650 v0 v1 v15
                                  (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v3) (coe v11)) v12
                                  v13 v6 v7 v16 v17))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    (\ v16 v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_650 v0 v1 v15
                                  (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v10) (coe v3)) v12
                                  v13 v6 v7 v16 v17))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v10 v11 v12
        -> coe
             (\ v13 v14 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    (\ v16 v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_bridge'45'i_650 v0 v1 v15
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'42'__122
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v3))
                                        (coe v10))
                                     v12 v13 v6 v7 v16 v17))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                        v1 v15
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v10))
                                        v12 v13 v0 v6)
                                     (coe v17)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v10))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v1) (coe v15)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__122
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v10)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                 (coe v3))
                                              (coe v10))
                                           (coe v12) (coe v13))
                                        (coe v0) (coe v7))
                                     (coe v17)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_bridge'45'i_650 v0 v1 v15
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v10))
                                        v12 v13 v6 v7 v16 v17)))
                               v17)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v11 v13 v14 v15 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> coe
                    (\ v21 v22 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_650 v0 v1 v19
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v3))
                                  v14 v17 v6 v7 v21 v22)
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                     (coe v1) (coe v20) (coe v11) (coe v15) (coe v18) (coe v0)
                                     (coe v6))
                                  (coe v22))
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v1))
                                     (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1)
                                        (coe v20) (coe v11) (coe v15) (coe v18))
                                     (coe v0) (coe v7))
                                  (coe v22))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_bridge'45'c_668 v0 v1 v20 v11 v15 v18 v6 v7 v21 v22))
                               v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v11 v13 v14 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                      -> coe
                           (\ v23 v24 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   (\ v25 v26 v27 v28 ->
                                      coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 d_bridge'45'i_650 v0 v1 v18
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v11)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                    (coe v22))
                                                 v13 v16 v6 v7 v23 v28)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                                    (coe v1) (coe v19) (coe v11) (coe v14) (coe v17)
                                                    (coe v0) (coe v6))
                                                 (coe v28))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                       (coe v1))
                                                    (coe v11)
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                       (coe v1) (coe v19) (coe v11) (coe v14)
                                                       (coe v17))
                                                    (coe v0) (coe v7))
                                                 (coe v28))
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                 (coe
                                                    d_bridge'45'c_668 v0 v1 v19 v11 v14 v17 v6 v7
                                                    v23 v28))
                                              v28)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.bridge-c
d_bridge'45'c_668 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'c_668 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
        -> coe
             (\ v14 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v15 v16 v17 v18 ->
                        coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v17))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v16 v17 v18 v19 ->
                        coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v18)))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v16 v17 v18 v19 ->
                        coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v18)))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
        -> coe
             (\ v14 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v15 v16 v17 v18 ->
                        coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
        -> coe
             (\ v14 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe (\ v15 v16 -> MAlonzo.RTE.mazUnreachableError)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v16 v17 v18 v19 ->
                        coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v18))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     (\ v16 v17 v18 v19 ->
                        coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v18))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v13 v16 v17 v19 v20
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v25 v26 v27
                             -> case coe v26 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v28 v29
                                    -> coe
                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                            (coe v1) (coe v24)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v29))
                                               (coe v27))
                                            (coe v16) (coe v19) (coe v0) (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v29))
                                               (coe v27))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                               (coe v1) (coe v24)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v29))
                                                  (coe v27))
                                               (coe v16) (coe v19))
                                            (coe v0) (coe v7))
                                         (coe
                                            d_bridge'45'c_668 (coe v0) (coe v1) (coe v24)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v29))
                                               (coe v27))
                                            (coe v16) (coe v19) (coe v6) (coe v7) (coe v8))
                                         (coe
                                            (\ v30 v31 v32 ->
                                               coe
                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                                    (coe v1) (coe v22)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v25)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v29))
                                                       (coe v13))
                                                    (coe v17) (coe v20) (coe v0) (coe v6))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v25)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v29))
                                                       (coe v13))
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                       (coe v1) (coe v22)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                          (coe v25)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                             (coe v29))
                                                          (coe v13))
                                                       (coe v17) (coe v20))
                                                    (coe v0) (coe v7))
                                                 (coe
                                                    d_bridge'45'c_668 (coe v0) (coe v1) (coe v22)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v25)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v29))
                                                       (coe v13))
                                                    (coe v17) (coe v20) (coe v6) (coe v7) (coe v8))
                                                 (coe
                                                    (\ v33 v34 v35 v36 ->
                                                       coe
                                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                         (coe
                                                            (\ v37 v38 v39 ->
                                                               coe
                                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                                 (coe v33 v37) (coe v34 v38)
                                                                 (coe v35 v37 v38 v39)
                                                                 (coe v32)))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v16 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v27 v28
                                    -> case coe v25 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v29 v30
                                           -> coe
                                                MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                                   (coe v1) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v16) (coe v18) (coe v0) (coe v6))
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                      (coe v1))
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe
                                                      MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                      (coe v1) (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                         (coe v27)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                            (coe v30))
                                                         (coe v26))
                                                      (coe v16) (coe v18))
                                                   (coe v0) (coe v7))
                                                (coe
                                                   d_bridge'45'c_668 (coe v0) (coe v1) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v16) (coe v18) (coe v6) (coe v7) (coe v8))
                                                (coe
                                                   (\ v31 v32 v33 ->
                                                      coe
                                                        MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                                           (coe v1) (coe v21)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe v28)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v30))
                                                              (coe v26))
                                                           (coe v17) (coe v19) (coe v0) (coe v6))
                                                        (coe
                                                           MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                              (coe v1))
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe v28)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v30))
                                                              (coe v26))
                                                           (coe
                                                              MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                              (coe v1) (coe v21)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                 (coe v28)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                    (coe v30))
                                                                 (coe v26))
                                                              (coe v17) (coe v19))
                                                           (coe v0) (coe v7))
                                                        (coe
                                                           d_bridge'45'c_668 (coe v0) (coe v1)
                                                           (coe v21)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe v28)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v30))
                                                              (coe v26))
                                                           (coe v17) (coe v19) (coe v6) (coe v7)
                                                           (coe v8))
                                                        (coe
                                                           (\ v34 v35 v36 v37 ->
                                                              coe
                                                                MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                                (coe
                                                                   (\ v38 v39 ->
                                                                      coe
                                                                        du_copair'45'rel_586
                                                                        (coe v33) (coe v36)
                                                                        (coe v38) (coe v39)))))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v15 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v23 v24 v25
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v26 v27
                                    -> coe
                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                            (coe v1) (coe v22)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v26))
                                            (coe v15) (coe v17) (coe v0) (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v26))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                               (coe v1) (coe v22)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe v23)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                  (coe v26))
                                               (coe v15) (coe v17))
                                            (coe v0) (coe v7))
                                         (coe
                                            d_bridge'45'c_668 (coe v0) (coe v1) (coe v22)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v26))
                                            (coe v15) (coe v17) (coe v6) (coe v7) (coe v8))
                                         (coe
                                            (\ v28 v29 v30 ->
                                               coe
                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                                    (coe v1) (coe v20)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v23)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v27))
                                                    (coe v16) (coe v18) (coe v0) (coe v6))
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v23)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v27))
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                       (coe v1) (coe v20)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                          (coe v23)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                          (coe v27))
                                                       (coe v16) (coe v18))
                                                    (coe v0) (coe v7))
                                                 (coe
                                                    d_bridge'45'c_668 (coe v0) (coe v1) (coe v20)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v23)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v27))
                                                    (coe v16) (coe v18) (coe v6) (coe v7) (coe v8))
                                                 (coe
                                                    (\ v31 v32 v33 v34 ->
                                                       coe
                                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                         (coe
                                                            (\ v35 v36 v37 ->
                                                               coe
                                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                                 (coe v28 v35) (coe v29 v36)
                                                                 (coe v30 v35 v36 v37)
                                                                 (coe
                                                                    (\ v38 v39 v40 ->
                                                                       coe
                                                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                                                         (coe v31 v35) (coe v32 v36)
                                                                         (coe v33 v35 v36 v37)
                                                                         (coe
                                                                            (\ v41 v42 v43 v44 ->
                                                                               coe
                                                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v40)
                                                                                    (coe
                                                                                       v43))))))))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v15
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                     (coe v1) (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v18) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v23))
                                     (coe v4) (coe v15) (coe v0) (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v1))
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v18) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v23))
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v1)
                                        (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__122 (coe v18)
                                              (coe v21))
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v23))
                                        (coe v4) (coe v15))
                                     (coe v0) (coe v7))
                                  (coe
                                     d_bridge'45'c_668 (coe v0) (coe v1) (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v18) (coe v21))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v23))
                                     (coe v4) (coe v15) (coe v6) (coe v7) (coe v8))
                                  (coe
                                     (\ v24 v25 v26 v27 ->
                                        coe
                                          MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                          (coe
                                             (\ v28 v29 v30 v31 ->
                                                coe
                                                  MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                  (coe
                                                     (\ v32 v33 v34 ->
                                                        coe
                                                          v26
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v28) (coe v32))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v29) (coe v33))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v30) (coe v34))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v21
                             -> case coe v19 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> coe
                                         MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'bind_130
                                         (coe
                                            MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_176
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe v1)))
                                            (coe v17)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                  (coe v21) (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v20))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                        (coe v1)))))
                                            (coe v15) (coe v0)
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                     (coe v1))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                     (coe v1))))
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                  (coe v21) (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v20))
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                     (coe v1))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                     (coe v1)))
                                               (coe v17)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe
                                                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                     (coe v21) (coe v20))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v23))
                                                  (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                           (coe v1)))))
                                               (coe v15))
                                            (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                         (coe
                                            d_bridge'45'c_668 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe v1)))
                                            (coe v17)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                  (coe v21) (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                               (coe v20))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                        (coe v1)))))
                                            (coe v15) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                         (coe
                                            (\ v24 v25 v26 v27 ->
                                               coe
                                                 MAlonzo.Code.Once.Adequacy.MeaningRelation.du_RelT'45'return_108
                                                 (\ v28 v29 v30 v31 ->
                                                    coe
                                                      MAlonzo.Code.Once.Adequacy.CataBridge.du_cata'45'bridge_76
                                                      (coe v21) (coe v14) (coe v24) (coe v25)
                                                      (coe v26) v28 v31)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516 v13
        -> coe d_bridge'45'i_650 v0 v1 v2 v3 v4 v13 v6 v7 v8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v15 v18
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v19 v20
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                      -> coe
                           (\ v24 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   (\ v25 v26 v27 ->
                                      d_bridge'45'c_668
                                        (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                           (coe v1) (coe v19) (coe v21))
                                        (coe v20) (coe v23)
                                        (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v4)
                                        (coe v18)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           (coe v25))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe v26))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe v27)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550 v14 v15 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v20 v21
                      -> coe
                           (\ v22 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'c_668 v0 v1 v18 v20 v14 v16 v6 v7 v8 v22))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'c_668 v0 v1 v19 v21 v15 v17 v6 v7 v8 v22))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560 v12 v13 v14
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe du_in'45'app'45'bridge_526)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_bridge'45'i_650 v0 v1 v16
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'42'__122
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v3))
                                        (coe v11))
                                     v13 v14 v6 v7 v8 v17))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                        v1 v16
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v11))
                                        v13 v14 v0 v6)
                                     (coe v17)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v11))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v1) (coe v16)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__122
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                 (coe v3))
                                              (coe v11))
                                           (coe v13) (coe v14))
                                        (coe v0) (coe v7))
                                     (coe v17)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_bridge'45'i_650 v0 v1 v16
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v3))
                                           (coe v11))
                                        v13 v14 v6 v7 v8 v17)))
                               v17)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                      -> coe
                           (\ v19 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe d_bridge'45'c_668 v0 v1 v16 v17 v13 v14 v6 v7 v8 v19)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                      -> coe
                           (\ v19 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe d_bridge'45'c_668 v0 v1 v16 v18 v13 v14 v6 v7 v8 v19)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606 v12 v13
        -> coe (\ v14 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> coe
                    d_bridge'45'c_668 (coe v0) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v17))
                    (coe v4) (coe v14) (coe v6) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634 v12 v14 v15 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> coe
                    (\ v21 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'c_668 v0 v1 v19
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v3))
                                  v14 v18 v6 v7 v8 v21)
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_186
                                     v1 v20 v12 v15 v17 v0 v6)
                                  (coe v21))
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v1))
                                     (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                        (coe v1) (coe v20) (coe v12) (coe v15) (coe v17))
                                     (coe v0) (coe v7))
                                  (coe v21))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_bridge'45'i_650 v0 v1 v20 v12 v15 v17 v6 v7 v8 v21))
                               v21)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648 v12 v13 v14 v21
        -> coe
             (\ v22 ->
                coe
                  d_bridge'45'c_668 v0
                  (MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v1))
                     (coe v14))
                  v13 v3
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v1))
                           (coe v14))))
                  v21 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v22)
      _ -> MAlonzo.RTE.mazUnreachableError
