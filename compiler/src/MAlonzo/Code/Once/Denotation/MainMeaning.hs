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

module MAlonzo.Code.Once.Denotation.MainMeaning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.MainMeaning.MClo
d_MClo_6 :: ()
d_MClo_6 = erased
-- Once.Denotation.MainMeaning.mainMeaningᵈ-go
d_mainMeaning'7496''45'go_20 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496''45'go_20 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v9 v10 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v16
                      -> case coe v16 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                             -> coe
                                  seq (coe v18)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                     (coe
                                        (\ v19 ->
                                           MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_278
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                                                (coe v2) (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.d_funName_106 (coe v14))
                                                (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                                             (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v14))
                                             (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42)
                                             (coe v10) (coe v12) (coe v3)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.d_env0_304
                                                (coe v10)
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                      -> coe
                           d_mmd'45'dispatch_46 (coe v0)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v14))
                           (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v14)) (coe v15)
                           (coe v2) (coe v9) (coe v10) (coe v3) (coe v12) (coe v13) (coe v16)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v14))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v9)
                              (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mmd-dispatch
d_mmd'45'dispatch_46 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mmd'45'dispatch_46 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = case coe v11 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
        -> if coe v14
             then coe
                    seq (coe v15)
                    (case coe v12 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                         -> if coe v16
                              then coe
                                     seq (coe v17)
                                     (if coe v13
                                        then coe
                                               d_mainMeaning'7496''45'go_20 (coe v0) (coe v3)
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                  (coe v4) (coe v1) (coe v5))
                                               (coe v7) (coe v9) (coe v10)
                                        else coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                               (coe
                                                  (\ v18 ->
                                                     MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_278
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                                                          (coe v4) (coe v0) (coe v1)
                                                          (coe
                                                             MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                                                       (coe v2)
                                                       (coe
                                                          MAlonzo.Code.Once.Spec.Module.d_EffUU_42)
                                                       (coe v6) (coe v8) (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Once.Denotation.Phase.d_env0_304
                                                          (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
                              else coe
                                     seq (coe v17)
                                     (coe
                                        d_mainMeaning'7496''45'go_20 (coe v0) (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                                           (coe v1) (coe v5))
                                        (coe v7) (coe v9) (coe v10))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v15)
                    (coe
                       d_mainMeaning'7496''45'go_20 (coe v0) (coe v3)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4) (coe v1)
                          (coe v5))
                       (coe v7) (coe v9) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mainMeaningᵈ-ef
d_mainMeaning'7496''45'ef_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496''45'ef_120 v0 ~v1 v2 v3 ~v4 v5
  = du_mainMeaning'7496''45'ef_120 v0 v2 v3 v5
du_mainMeaning'7496''45'ef_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mainMeaning'7496''45'ef_120 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    d_mainMeaning'7496''45'go_20
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v6))
                    (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64) (coe v0)
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mainMeaningᵈ
d_mainMeaning'7496'_144 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496'_144 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> coe
             du_mainMeaning'7496''45'ef_120 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.d_extractFunctions_514
                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                (coe v1))
             (coe v2) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.runMainᵈ
d_runMain'7496'_156 ::
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]
d_runMain'7496'_156 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_trT_18
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
         (coe v0 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         (coe (\ v2 -> coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      v1
-- Once.Denotation.MainMeaning.mainMeaningᵈ-pf
d_mainMeaning'7496''45'pf_174
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.MainMeaning.mainMeaning\7496-pf"
-- Once.Denotation.MainMeaning.meaningᵈ
d_meaning'7496'_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.Behavior.T_Behavior_6
d_meaning'7496'_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.Behavior.C_mkBehavior_40
      (d_runMain'7496'_156
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_mainMeaning'7496'_144 (coe v0) (coe v1) (coe v2) (coe v3))))
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_coh_412
         (coe d_pf_196 (coe v0) (coe v1) (coe v2) (coe v3)))
      (MAlonzo.Code.Once.Denotation.TraceMonad.d_bnd_408
         (coe d_pf_196 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.Denotation.MainMeaning._.pf
d_pf_196 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_396
d_pf_196 v0 v1 v2 v3
  = coe d_mainMeaning'7496''45'pf_174 v0 v1 v2 v3
