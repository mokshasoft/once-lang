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
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.MeaningBridge.subst-∘-move
d_subst'45''8728''45'move_24 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8728''45'move_24 = erased
-- Once.Adequacy.MeaningBridge.RelEnv
d_RelEnv_34 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  AgdaAny -> AgdaAny -> ()
d_RelEnv_34 = erased
-- Once.Adequacy.MeaningBridge.rel-lookup
d_rel'45'lookup_60 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_rel'45'lookup_60 ~v0 v1 v2 v3 v4 v5
  = du_rel'45'lookup_60 v1 v2 v3 v4 v5
du_rel'45'lookup_60 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_rel'45'lookup_60 v0 v1 v2 v3 v4
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
                                         du_rel'45'lookup_60 (coe v6) (coe v10) (coe v11) (coe v13)
                                         (coe v15)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.base-rel→eq
d_base'45'rel'8594'eq_104 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'rel'8594'eq_104 = erased
-- Once.Adequacy.MeaningBridge.wfF-layer-eq
d_wfF'45'layer'45'eq_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_wfF'45'layer'45'eq_178 = erased
-- Once.Adequacy.MeaningBridge.base-rel→refl
d_base'45'rel'8594'refl_256 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_base'45'rel'8594'refl_256 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_base'45'rel'8594'refl_256 (coe v7) (coe v5) (coe v9))
                           (coe d_base'45'rel'8594'refl_256 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe d_base'45'rel'8594'refl_256 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe d_base'45'rel'8594'refl_256 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.concrete-rel→refl
d_concrete'45'rel'8594'refl_294 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> AgdaAny
d_concrete'45'rel'8594'refl_294 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v4
        -> coe d_base'45'rel'8594'refl_256 (coe v0) (coe v4) (coe v2)
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v8 v9 v10
               -> coe
                    (\ v11 v12 v13 ->
                       d_RelT'45'refl_302 (coe v10) (coe v7) (coe v2 v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.RelT-refl
d_RelT'45'refl_302 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_RelT'45'refl_302 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         d_concrete'45'rel'8594'refl_294 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70 (coe v2)
            (coe v3)))
-- Once.Adequacy.MeaningBridge.sigop-bridge
d_sigop'45'bridge_344 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'bridge_344 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_sigop'45'bridge_344 v0 v1 v2 v3 v4 v5 v8
du_sigop'45'bridge_344 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'bridge_344 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         d_concrete'45'rel'8594'refl_294 (coe v1) (coe v4)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (\ v7 ->
               coe
                 MAlonzo.Code.Once.Denotation.Meaning.du_named'45'sem_60 (coe v0)
                 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
            (coe v6)))
-- Once.Adequacy.MeaningBridge.sd-sigOp-base≡
d_sd'45'sigOp'45'base'8801'_382 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sd'45'sigOp'45'base'8801'_382 = erased
-- Once.Adequacy.MeaningBridge.sigop-ref-bridge
d_sigop'45'ref'45'bridge_436 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'ref'45'bridge_436 ~v0 ~v1 v2 v3 v4 ~v5
  = du_sigop'45'ref'45'bridge_436 v2 v3 v4
du_sigop'45'ref'45'bridge_436 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'ref'45'bridge_436 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v4
        -> coe
             d_RelT'45'refl_302 (coe v0)
             (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v4)
             (coe
                MAlonzo.Code.Once.Denotation.Meaning.d_sigOpRef'7472'_236 (coe v0)
                (coe v1)
                (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v4))
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v6 v7
        -> coe
             d_RelT'45'refl_302 (coe v0)
             (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v6 v7)
             (coe
                MAlonzo.Code.Once.Denotation.Meaning.d_sigOpRef'7472'_236 (coe v0)
                (coe v1)
                (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v6 v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.in-app-bridge
d_in'45'app'45'bridge_470 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_in'45'app'45'bridge_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_in'45'app'45'bridge_470
du_in'45'app'45'bridge_470 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_in'45'app'45'bridge_470
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.MeaningBridge.int-bridge
d_int'45'bridge_490 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_int'45'bridge_490 ~v0 ~v1 ~v2 ~v3 ~v4 = du_int'45'bridge_490
du_int'45'bridge_490 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_int'45'bridge_490
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Adequacy.MeaningBridge.bridge-g
d_bridge'45'g_510 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'g_510 ~v0 v1 v2 ~v3 v4 ~v5
  = du_bridge'45'g_510 v1 v2 v4
du_bridge'45'g_510 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bridge'45'g_510 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_318
        -> coe (\ v5 -> coe du_int'45'bridge_490)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_330 v7 v8
        -> coe
             (\ v9 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_334
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_346 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                      -> coe
                           (\ v14 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe du_bridge'45'g_510 v10 v12 v8 v14))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe du_bridge'45'g_510 v11 v13 v9 v14))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_356 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           (\ v12 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe du_bridge'45'g_510 v9 v10 v7 v12)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_366 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           (\ v12 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe du_bridge'45'g_510 v9 v11 v7 v12)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_376 v6 v8
        -> coe
             (\ v9 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge._.g-In-reduce
d_g'45'In'45'reduce_626 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_g'45'In'45'reduce_626 = erased
-- Once.Adequacy.MeaningBridge.wrapM
d_wrapM_652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_wrapM_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_wrapM_652 v8 v9 v10
du_wrapM_652 ::
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_wrapM_652 v0 v1 v2 = coe v0 v1 v2
-- Once.Adequacy.MeaningBridge.bridge-m
d_bridge'45'm_678 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'm_678 ~v0 v1 v2 v3 ~v4 v5 v6 v7
  = du_bridge'45'm_678 v1 v2 v3 v5 v6 v7
du_bridge'45'm_678 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bridge'45'm_678 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_384
        -> coe
             du_wrapM_652
             (coe
                (\ v11 v12 v13 v14 ->
                   coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v13)))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_394
        -> coe
             du_wrapM_652
             (coe
                (\ v12 v13 v14 v15 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v14))))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_404
        -> coe
             du_wrapM_652
             (coe
                (\ v12 v13 v14 v15 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v14))))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_412
        -> coe
             du_wrapM_652
             (coe
                (\ v11 v12 v13 v14 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_430
        -> coe
             du_wrapM_652
             (coe
                (\ v12 v13 v14 v15 ->
                   coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v14)))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_440
        -> coe
             du_wrapM_652
             (coe
                (\ v12 v13 v14 v15 ->
                   coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v14)))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_456 v10 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> coe
                           du_wrapM_652
                           (coe
                              (\ v20 v21 v22 v23 ->
                                 coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         du_bridge'45'm_678 v19 v10 v2 v14
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.du_'10214'_'10215''7504'_108
                                               v17 v1 v10 v15 v20)
                                            (coe v23))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_328
                                               (coe v1) (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Realize.du_realize'45'morph_72
                                                  (coe v17) (coe v1) (coe v10) (coe v15))
                                               (coe v21))
                                            (coe v23))
                                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe du_bridge'45'm_678 v17 v1 v10 v15 v20 v21 v22 v23))
                                         v23))))
                           (coe v4) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_472 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v19 v20
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                                    -> case coe v5 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                                           -> coe
                                                (\ v23 ->
                                                   coe
                                                     du_bridge'45'm_678 v18 v19 v2 v13 v21 v22 v23)
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                                           -> coe (\ v23 -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                                    -> case coe v5 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                                           -> coe (\ v23 -> MAlonzo.RTE.mazUnreachableError)
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                                           -> coe
                                                (\ v23 ->
                                                   coe
                                                     du_bridge'45'm_678 v16 v20 v2 v14 v21 v22 v23)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_486 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                             -> coe
                                  du_wrapM_652
                                  (coe
                                     (\ v20 v21 v22 v23 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_bridge'45'm_678 v17 v1 v18 v12 v20 v21 v22
                                                   v23))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   du_bridge'45'm_678 v15 v1 v19 v13 v20 v21 v22
                                                   v23)))))
                                  (coe v4) (coe v5)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_498 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                      -> coe
                           du_wrapM_652
                           (coe
                              (\ v17 v18 v19 v20 ->
                                 coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                   (coe
                                      (\ v21 v22 v23 ->
                                         coe
                                           du_bridge'45'm_678 v13
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__126 (coe v1)
                                              (coe v14))
                                           v16 v11
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                              (coe v21))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              (coe v22))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19)
                                              (coe v23))))))
                           (coe v4) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_512 v11 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                      -> coe
                           (\ v17 ->
                              coe
                                MAlonzo.Code.Once.Adequacy.CataBridge.du_cata'45'bridge_66
                                (coe v16) (coe v2) (coe v11)
                                (coe
                                   MAlonzo.Code.Once.Denotation.Meaning.du_'10214'_'10215''7504'_108
                                   (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                      (coe v2))
                                   (coe v2) (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.du_realize'45'morph_72
                                   (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                      (coe v2))
                                   (coe v2) (coe v13))
                                (coe
                                   du_bridge'45'm_678 (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                      (coe v2))
                                   (coe v2) (coe v13))
                                (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_524 v11
        -> coe
             (\ v12 -> coe du_bridge'45'g_510 (coe v0) (coe v2) (coe v11))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_536 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe
                    (\ v17 ->
                       coe
                         du_sigop'45'bridge_344 (coe v1) (coe v2)
                         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v16)) (coe v14)
                         (coe v15) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_548 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v14
               -> coe
                    (\ v15 ->
                       coe
                         du_sigop'45'bridge_344 (coe v1) (coe v2) (coe v14) (coe v12)
                         (coe v13) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.≡→RelV-⊎⊤
d_'8801''8594'RelV'45''8846''8868'_878 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8801''8594'RelV'45''8846''8868'_878 v0 ~v1 ~v2
  = du_'8801''8594'RelV'45''8846''8868'_878 v0
du_'8801''8594'RelV'45''8846''8868'_878 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'8801''8594'RelV'45''8846''8868'_878 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Adequacy.MeaningBridge.SD-subst-usage
d_SD'45'subst'45'usage_898 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_SD'45'subst'45'usage_898 = erased
-- Once.Adequacy.MeaningBridge.bridge-i
d_bridge'45'i_916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'i_916 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe
             (\ v9 v10 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42 v11 v12
        -> coe
             (\ v13 v14 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> coe
             (\ v9 v10 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe
             (\ v8 v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe
             (\ v8 v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v11
        -> case coe v11 of
             MAlonzo.Code.Once.Surface.Context.C_svar_192 v16
               -> case coe v0 of
                    MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368 v17 v18 v19 v20 v21 v22 v23
                      -> coe
                           (\ v24 v25 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_rel'45'lookup_60 (coe v19) (coe v16) (coe v5) (coe v6)
                                   (coe v24)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         du_sigop'45'ref'45'bridge_436 (coe v2)
                         (coe
                            MAlonzo.Code.Once.CanonicalName.d_bare_12
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20 v14
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("." :: Data.Text.Text) v13)))
                         (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe
                    (\ v13 ->
                       coe du_sigop'45'ref'45'bridge_436 (coe v2) (coe v12) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
               -> coe
                    (\ v15 ->
                       coe
                         du_sigop'45'ref'45'bridge_436 (coe v2)
                         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v14))
                         (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v10 v11 v12 v13 v21
        -> coe
             (\ v22 v23 ->
                coe
                  d_bridge'45'c_934
                  (MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                     (coe v12))
                  v11 v2
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                           (coe v12))))
                  v21 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v23)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v12 v13
               -> coe
                    (\ v14 ->
                       d_bridge'45'c_934
                         (coe v0) (coe v12) (coe v2) (coe v3) (coe v11) (coe v5) (coe v6)
                         (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                      -> coe
                           (\ v20 v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'i_916 v0 v16 v18 v12 v14 v5 v6 v20 v21))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'i_916 v0 v17 v19 v13 v15 v5 v6 v20 v21))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v10
        -> coe
             (\ v11 v12 ->
                coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_164 v11 v13 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v18 v19 v20
               -> coe
                    (\ v21 v22 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_bridge'45'i_916
                               (MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                  (coe v0) (coe v18) (coe v11))
                               v20 v2
                               (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v13 v15) v17
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                        v0 v19 v11 v14 v16 v5)
                                     (coe v22)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v0))
                                        (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v0) (coe v19) (coe v11) (coe v14) (coe v16))
                                        (coe v6))
                                     (coe v22)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v21)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe d_bridge'45'i_916 v0 v19 v11 v14 v16 v5 v6 v21 v22)))
                               v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_194 v13 v14 v16 v17 v18 v19 v20 v21 v22 v23
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v24 v25 v26 v27 v28
               -> coe
                    (\ v29 v30 ->
                       let v31
                             = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                 (coe
                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                    v0 v24
                                    (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v13) (coe v14))
                                    v18 v21 v5 v30) in
                       coe
                         (let v32
                                = MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                       (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                          (coe v0))
                                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v13) (coe v14))
                                       (MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                          (coe v0) (coe v24)
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'43'__128 (coe v13)
                                             (coe v14))
                                          (coe v18) (coe v21))
                                       v6 v30) in
                          coe
                            (let v33
                                   = coe
                                       d_bridge'45'i_916 v0 v24
                                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v13) (coe v14))
                                       v18 v21 v5 v6 v29 v30 in
                             coe
                               (case coe v31 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v34
                                    -> case coe v32 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v35
                                           -> case coe v33 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             d_bridge'45'i_916
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                                      (coe v25) (coe v13)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                                   (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                      (coe v0))
                                                                   v13
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366
                                                                   (coe v0)))
                                                             v26 v2
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                                v16 v19)
                                                             v22
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v5) (coe v34))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v6) (coe v35))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v29) (coe v37))
                                                             v30))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v34
                                    -> case coe v32 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v35
                                           -> case coe v33 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             d_bridge'45'i_916
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                                      (coe v27) (coe v14)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                                   (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                      (coe v0))
                                                                   v14
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                                   (coe v0))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366
                                                                   (coe v0)))
                                                             v28 v2
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                                v17 v20)
                                                             v23
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v5) (coe v34))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v6) (coe v35))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v29) (coe v37))
                                                             v30))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_208 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v16 v17 v18
               -> coe
                    seq (coe v16)
                    (coe
                       (\ v19 v20 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_222 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_178
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_180
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_182
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_184
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_186
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           (\ v19 v20 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   du_'8801''8594'RelV'45''8846''8868'_878
                                   (coe
                                      MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_188
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v17 (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14
                                               v5)
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                               v0 v18 (coe MAlonzo.Code.Once.Type.C_Int_136) v12 v15
                                               v5)
                                            (coe v20))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_232 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    (\ v14 v15 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe d_bridge'45'i_916 v0 v13 v2 v10 v11 v5 v6 v14 v15)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_244 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 v16 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_916 v0 v14
                                  (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v10)) v11
                                  v12 v5 v6 v15 v16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_256 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 v16 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_916 v0 v14
                                  (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v9) (coe v2)) v11
                                  v12 v5 v6 v15 v16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_266 v9 v10 v11
        -> coe
             (\ v12 v13 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_278 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    (\ v15 v16 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_bridge'45'i_916 v0 v14
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'42'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v2))
                                        (coe v9))
                                     v11 v12 v5 v6 v15 v16))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                        v0 v14
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v9))
                                        v11 v12 v5)
                                     (coe v16)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v9))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v0) (coe v14)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__126
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                 (coe v2))
                                              (coe v9))
                                           (coe v11) (coe v12))
                                        (coe v6))
                                     (coe v16)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_bridge'45'i_916 v0 v14
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v9))
                                        v11 v12 v5 v6 v15 v16)))
                               v16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_296 v10 v12 v13 v14 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    (\ v20 v21 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'i_916 v0 v18
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v2))
                                  v13 v16 v5 v6 v20 v21)
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_272
                                     (coe v0) (coe v19) (coe v10) (coe v14) (coe v17) (coe v5))
                                  (coe v21))
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v0))
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0)
                                        (coe v19) (coe v10) (coe v14) (coe v17))
                                     (coe v6))
                                  (coe v21))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_bridge'45'c_934 v0 v19 v10 v14 v17 v5 v6 v20 v21))
                               v21)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_312 v10 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v19 v20 v21
                      -> coe
                           (\ v22 v23 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   (\ v24 v25 v26 v27 ->
                                      coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 d_bridge'45'i_916 v0 v17
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                    (coe v10)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                    (coe v21))
                                                 v12 v15 v5 v6 v22 v27)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_272
                                                    (coe v0) (coe v18) (coe v10) (coe v13) (coe v16)
                                                    (coe v5))
                                                 (coe v27))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                 (coe
                                                    MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                       (coe v0))
                                                    (coe v10)
                                                    (coe
                                                       MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                       (coe v0) (coe v18) (coe v10) (coe v13)
                                                       (coe v16))
                                                    (coe v6))
                                                 (coe v27))
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                 (coe
                                                    d_bridge'45'c_934 v0 v18 v10 v13 v16 v5 v6 v22
                                                    v27))
                                              v27)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MeaningBridge.bridge-c
d_bridge'45'c_934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bridge'45'c_934 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_560 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe du_bridge'45'm_678 (coe v1) (coe v14) (coe v16) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_570 v12
        -> coe d_bridge'45'i_916 v0 v1 v2 v3 v12 v5 v6 v7
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_588 v14 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v20 v21 v22
                      -> coe
                           (\ v23 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   (\ v24 v25 v26 ->
                                      d_bridge'45'c_934
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                           (coe v0) (coe v18) (coe v20))
                                        (coe v19) (coe v22)
                                        (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v3)
                                        (coe v17)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                           (coe v24))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           (coe v25))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe v26)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_600 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            (\ v18 v19 v20 ->
                               coe du_bridge'45'g_510 (coe v1) (coe v16) (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_616 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v19 v20
                      -> coe
                           (\ v21 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'c_934 v0 v17 v19 v13 v15 v5 v6 v7 v21))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe d_bridge'45'c_934 v0 v18 v20 v14 v16 v5 v6 v7 v21))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_628 v11 v12 v14
        -> coe
             (\ v15 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe du_in'45'app'45'bridge_470)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_640 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_bridge'45'i_916 v0 v15
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'42'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v2))
                                        (coe v10))
                                     v12 v13 v5 v6 v7 v16))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                        v0 v15
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v10))
                                        v12 v13 v5)
                                     (coe v16)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                           (coe v0))
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v10))
                                        (coe
                                           MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                           (coe v0) (coe v15)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__126
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                 (coe v10)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                 (coe v2))
                                              (coe v10))
                                           (coe v12) (coe v13))
                                        (coe v6))
                                     (coe v16)))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_bridge'45'i_916 v0 v15
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_pure_34))
                                              (coe v2))
                                           (coe v10))
                                        v12 v13 v5 v6 v7 v16)))
                               v16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_652 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v16 v17
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe d_bridge'45'c_934 v0 v15 v16 v12 v13 v5 v6 v7 v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_664 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v16 v17
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe d_bridge'45'c_934 v0 v15 v17 v12 v13 v5 v6 v7 v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_674 v11 v12
        -> coe (\ v13 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_686 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    d_bridge'45'c_934 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v16))
                    (coe v3) (coe v13) (coe v5) (coe v6) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_702 v11 v13 v14 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    (\ v20 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_bridge'45'c_934 v0 v18
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v2))
                                  v13 v17 v5 v6 v7 v20)
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7522'_282
                                     v0 v19 v11 v14 v16 v5)
                                  (coe v20))
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                  (coe
                                     MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_110
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                        (coe v0))
                                     (coe v11)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                        (coe v0) (coe v19) (coe v11) (coe v14) (coe v16))
                                     (coe v6))
                                  (coe v20))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe d_bridge'45'i_916 v0 v19 v11 v14 v16 v5 v6 v7 v20))
                               v20)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_716 v11 v12 v13 v20
        -> coe
             (\ v21 ->
                coe
                  d_bridge'45'c_934
                  (MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                     (coe v13))
                  v12 v2
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                           (coe v13))))
                  v20 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) v21)
      _ -> MAlonzo.RTE.mazUnreachableError
