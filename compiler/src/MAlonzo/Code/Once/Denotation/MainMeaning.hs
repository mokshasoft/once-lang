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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.ModuleComplete
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.MainMeaning.MClo
d_MClo_6 :: ()
d_MClo_6 = erased
-- Once.Denotation.MainMeaning.mainMeaningᵈ-go
d_mainMeaning'7496''45'go_20 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496''45'go_20 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v9 v10 v12 v13
        -> case coe v2 of
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
                                        MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_272
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                           (coe (0 :: Integer))
                                           (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                           (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                           (coe (0 :: Integer))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_funName_108
                                                    (coe v14))
                                                 (coe
                                                    MAlonzo.Code.Once.Adequacy.ModuleComplete.d_EffUU_6))
                                              (coe v3))
                                           (coe v0) (coe v1))
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14))
                                        (coe MAlonzo.Code.Once.Adequacy.ModuleComplete.d_EffUU_6)
                                        (coe v10) (coe v12)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                      -> coe
                           d_mmd'45'dispatch_46 (coe v0) (coe v1)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                           (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14)) (coe v15)
                           (coe v3) (coe v9) (coe v10) (coe v12) (coe v13) (coe v16)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240 (coe v9)
                              (coe MAlonzo.Code.Once.Adequacy.ModuleComplete.d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mmd-dispatch
d_mmd'45'dispatch_46 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
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
                                               d_mainMeaning'7496''45'go_20 (coe v0) (coe v1)
                                               (coe v4)
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                  (coe v5) (coe v2) (coe v6))
                                               (coe v9) (coe v10)
                                        else coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Meaning.d_'10214'_'10215''7580'_272
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v2)
                                                           (coe
                                                              MAlonzo.Code.Once.Adequacy.ModuleComplete.d_EffUU_6))
                                                        (coe v5))
                                                     (coe v0) (coe v1))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Once.Adequacy.ModuleComplete.d_EffUU_6)
                                                  (coe v7) (coe v8)))
                              else coe
                                     seq (coe v17)
                                     (coe
                                        d_mainMeaning'7496''45'go_20 (coe v0) (coe v1) (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                                           (coe v2) (coe v6))
                                        (coe v9) (coe v10))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v15)
                    (coe
                       d_mainMeaning'7496''45'go_20 (coe v0) (coe v1) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5) (coe v2)
                          (coe v6))
                       (coe v9) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mainMeaningᵈ-ef
d_mainMeaning'7496''45'ef_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496''45'ef_102 v0 v1 v2 ~v3 v4
  = du_mainMeaning'7496''45'ef_102 v0 v1 v2 v4
du_mainMeaning'7496''45'ef_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mainMeaning'7496''45'ef_102 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    d_mainMeaning'7496''45'go_20
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v6))
                    (coe
                       MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                    (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) (coe v2)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.mainMeaningᵈ
d_mainMeaning'7496'_122 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainMeaning'7496'_122 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             du_mainMeaning'7496''45'ef_102 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.d_extractFunctions_540
                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                (coe v0))
             (coe v1) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.MainMeaning.runMainᵈ
d_runMain'7496'_132 ::
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_runMain'7496'_132 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
            (coe v0 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe (\ v2 -> coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
         (coe v1))
-- Once.Denotation.MainMeaning.meaningᵈ
d_meaning'7496'_144 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_meaning'7496'_144 v0 v1 v2
  = coe
      d_runMain'7496'_132
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_mainMeaning'7496'_122 (coe v0) (coe v1) (coe v2)))
