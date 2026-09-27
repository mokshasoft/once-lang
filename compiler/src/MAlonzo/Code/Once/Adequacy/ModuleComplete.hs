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

module MAlonzo.Code.Once.Adequacy.ModuleComplete where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ModuleComplete.compileFunBody-complete
d_compileFunBody'45'complete_20 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'complete_20 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_984
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                  (coe v0) (coe v1) (coe v2) (coe v3)))
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                  (coe v0) (coe v1) (coe v2) (coe v3)))
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v3)
            (coe
               MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3916
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                     (coe v0) (coe v1) (coe v2) (coe v3)))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                     (coe v0) (coe v1) (coe v2) (coe v3)))
               (coe v3) (coe v1)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                  (coe v0))
               (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_5542
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                        (coe v0) (coe v1) (coe v2) (coe v3))
                     (coe v4) (coe v3) (coe v6)))))
         erased)
-- Once.Adequacy.ModuleComplete.compileFun-complete
d_compileFun'45'complete_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'complete_56 v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_compileFun'45'complete_56 v0 v1 v2 v3 v4 v5 v7
du_compileFun'45'complete_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'complete_56 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v2))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          d_compileFunBody'45'complete_20 (coe v0) (coe v1) (coe v2)
                          (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42) (coe v4) (coe v5)
                          (coe v6))
                else coe
                       seq (coe v9)
                       (coe
                          d_compileFunBody'45'complete_20 (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe v4) (coe v5) (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.caf-go-complete
d_caf'45'go'45'complete_138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'complete_138 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_tnil_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v8 v9 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                                 (coe
                                    MAlonzo.Code.Once.CanonicalName.d_bare_12
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                                       (coe v8)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_compileFun'45'complete_56 (coe v2) (coe v0)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                                             (coe v8)
                                             (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v13))
                                             (coe v9) (coe v11)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                                       (coe v8)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_compileFun'45'complete_56 (coe v2) (coe v0)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                                             (coe v8)
                                             (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v13))
                                             (coe v9) (coe v11)))))
                                 (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v13)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    d_caf'45'go'45'complete_138 (coe v0) (coe v14)
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                                       (coe v8))
                                    (coe v12) (coe v16))))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.findMain-main-or-skip
d_findMain'45'main'45'or'45'skip_182 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findMain'45'main'45'or'45'skip_182 v0 v1 ~v2 v3 v4
  = du_findMain'45'main'45'or'45'skip_182 v0 v1 v3 v4
du_findMain'45'main'45'or'45'skip_182 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_findMain'45'main'45'or'45'skip_182 v0 v1 v2 v3
  = if coe v1
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8 (coe v0)) erased
-- Once.Adequacy.ModuleComplete.FindResult
d_FindResult_206 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_FindResult_206 = erased
-- Once.Adequacy.ModuleComplete.caf-go-find-complete
d_caf'45'go'45'find'45'complete_226 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'find'45'complete_226 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v9 v10 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                    -> case coe v14 of
                                         MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v21 v22 v23 v24
                                           -> coe
                                                seq (coe v20)
                                                (let v25
                                                       = d_compileFunBody'45'complete_20
                                                           (coe v2) (coe v0)
                                                           (coe ("main" :: Data.Text.Text))
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Module.d_EffUU_42)
                                                           (coe v23) (coe v10) (coe v12) in
                                                 coe
                                                   (case coe v25 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                        -> let v28
                                                                 = d_caf'45'go'45'complete_138
                                                                     (coe v0) (coe v15)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                                        (coe v2)
                                                                        (coe
                                                                           ("main"
                                                                            ::
                                                                            Data.Text.Text))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                                                                     (coe v13) (coe v17) in
                                                           coe
                                                             (case coe v28 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                                                                             (coe
                                                                                MAlonzo.Code.Once.CanonicalName.d_bare_12
                                                                                (coe
                                                                                   ("main"
                                                                                    ::
                                                                                    Data.Text.Text)))
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Unit_118)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8
                                                                                (coe v26))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                                                          (coe v29))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8
                                                                             (coe v26))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             erased erased))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                             -> let v19
                                      = d_caf'45'go'45'find'45'complete_226
                                          (coe v0) (coe v15)
                                          (coe
                                             MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v14))
                                             (coe v9))
                                          (coe v13) (coe v17) (coe v18) in
                                coe
                                  (let v20 = MAlonzo.Code.Once.Parser.d_funName_106 (coe v14) in
                                   coe
                                     (let v21
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v21 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.d_funName_106
                                                        (coe v14)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                      (MAlonzo.Code.Once.Parser.d_funName_106
                                                         (coe v14)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                      ("main" :: Data.Text.Text))) in
                                      coe
                                        (let v22
                                               = MAlonzo.Code.Once.Parser.d_funBody_110 (coe v14) in
                                         coe
                                           (case coe v21 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                -> if coe v23
                                                     then let v25
                                                                = seq
                                                                    (coe v24)
                                                                    (coe
                                                                       d_compileFunBody'45'complete_20
                                                                       (coe v2) (coe v0) (coe v20)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Spec.Module.d_EffUU_42)
                                                                       (coe v22) (coe v10)
                                                                       (coe v12)) in
                                                          coe
                                                            (case coe v25 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                 -> case coe v19 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                        -> case coe v29 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                               -> coe
                                                                                    seq (coe v31)
                                                                                    (coe
                                                                                       du_result_392
                                                                                       (coe v14)
                                                                                       (coe v9)
                                                                                       (coe v26)
                                                                                       (coe v28)
                                                                                       (coe v30))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     else (let v25
                                                                 = seq
                                                                     (coe v24)
                                                                     (coe
                                                                        d_compileFunBody'45'complete_20
                                                                        (coe v2) (coe v0) (coe v20)
                                                                        (coe v9) (coe v22) (coe v10)
                                                                        (coe v12)) in
                                                           coe
                                                             (case coe v25 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                  -> case coe v19 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                         -> case coe v29 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                -> coe
                                                                                     seq (coe v31)
                                                                                     (coe
                                                                                        du_result_392
                                                                                        (coe v14)
                                                                                        (coe v9)
                                                                                        (coe v26)
                                                                                        (coe v28)
                                                                                        (coe v30))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.findMain-main-here
d_findMain'45'main'45'here_318 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'main'45'here_318 = erased
-- Once.Adequacy.ModuleComplete._.cf0
d_cf0_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_234
d_cf0_388 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17
  = du_cf0_388 v2 v4 v11
du_cf0_388 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_234
du_cf0_388 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)) (coe v1)
            (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)) (coe v1)
            (coe v2)))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v0))
-- Once.Adequacy.ModuleComplete._.ca-eq
d_ca'45'eq_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ca'45'eq_390 = erased
-- Once.Adequacy.ModuleComplete._.result
d_result_392 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_392 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
             v13 v14 ~v15 ~v16 ~v17
  = du_result_392 v2 v4 v11 v13 v14
du_result_392 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_392 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v5 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0))
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then coe
                       seq (coe v7)
                       (case coe v0 of
                          MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v8 v9 v10 v11
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                                       (coe
                                          MAlonzo.Code.Once.CanonicalName.d_bare_12
                                          (coe ("main" :: Data.Text.Text)))
                                       (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                       (coe MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8 (coe v2))
                                       (coe v11))
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          du_findMain'45'main'45'or'45'skip_182 (coe v2) (coe v11)
                                          (coe v4) erased))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_findMain'45'main'45'or'45'skip_182 (coe v2)
                                             (coe v11) (coe v4) erased))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe du_cf0_388 (coe v0) (coe v1) (coe v2)) (coe v3))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.moduleToIR-complete
d_moduleToIR'45'complete_412 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'complete_412 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> let v5
                 = MAlonzo.Code.Once.Parser.d_guardDistinct_500
                     (coe
                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_182
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                        (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> let v9
                                  = d_caf'45'go'45'find'45'complete_226
                                      (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v8))
                                      (coe v7) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64)
                                      (coe v1) (coe v3) (coe v4) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                   -> case coe v11 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                          -> coe
                                               seq (coe v13)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v12) erased)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mainRealized-go
d_mainRealized'45'go_472 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized'45'go_472 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v8 v9 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                      -> case coe v15 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                             -> coe
                                  seq (coe v17)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                           (coe (0 :: Integer))
                                           (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                           (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                           (coe (0 :: Integer))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_funName_106
                                                    (coe v13))
                                                 (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                                              (coe v2))
                                           (coe v0))
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v13))
                                        (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42) (coe v9)
                                        (coe v11)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                      -> coe
                           d_mrg'45'dispatch_496 (coe v0)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                           (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v13)) (coe v14)
                           (coe v2) (coe v8) (coe v9) (coe v11) (coe v12) (coe v15)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v13))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v8)
                              (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mrg-dispatch
d_mrg'45'dispatch_496 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mrg'45'dispatch_496 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
        -> if coe v13
             then coe
                    seq (coe v14)
                    (case coe v11 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                         -> if coe v15
                              then coe
                                     seq (coe v16)
                                     (if coe v12
                                        then coe
                                               d_mainRealized'45'go_472 (coe v0) (coe v3)
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                  (coe v4) (coe v1) (coe v5))
                                               (coe v8) (coe v9)
                                        else coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
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
                                                           (coe v1)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Module.d_EffUU_42))
                                                        (coe v4))
                                                     (coe v0))
                                                  (coe v2)
                                                  (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_42)
                                                  (coe v6) (coe v7)))
                              else coe
                                     seq (coe v16)
                                     (coe
                                        d_mainRealized'45'go_472 (coe v0) (coe v3)
                                        (coe
                                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                                           (coe v1) (coe v5))
                                        (coe v8) (coe v9))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v14)
                    (coe
                       d_mainRealized'45'go_472 (coe v0) (coe v3)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4) (coe v1)
                          (coe v5))
                       (coe v8) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mainRealized-ef
d_mainRealized'45'ef_552 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized'45'ef_552 ~v0 v1 v2 ~v3 v4
  = du_mainRealized'45'ef_552 v1 v2 v4
du_mainRealized'45'ef_552 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mainRealized'45'ef_552 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    d_mainRealized'45'go_472
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v5))
                    (coe v4) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64) (coe v1)
                    (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mainRealized
d_mainRealized_572 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized_572 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             du_mainRealized'45'ef_552
             (coe
                MAlonzo.Code.Once.Parser.d_extractFunctions_514
                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                (coe v0))
             (coe v1) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.caf-go-mains
d_caf'45'go'45'mains_592 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_caf'45'go'45'mains_592 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'go'45'mains_592 v0 v1 v2 v3
du_caf'45'go'45'mains_592 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 -> AgdaAny
du_caf'45'go'45'mains_592 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_tnil_14
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v7 v8 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> coe
                    du_go_622 (coe v0) (coe v2) (coe v12) (coe v13) (coe v7) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.go
d_go_622 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_622 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_go_622 v0 v1 v2 v3 v4 v8
du_go_622 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_622 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Compile.du_compileFun'45'aux_184
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) (coe v0)
              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> let v8
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v1)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             du_caf'45'go'45'mains_592 (coe v0) (coe v3)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v1)
                                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                             (coe v5))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.findMain-skip-prim
d_findMain'45'skip'45'prim_668 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_234 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip'45'prim_668 = erased
-- Once.Adequacy.ModuleComplete.caf-go-mainexists
d_caf'45'go'45'mainexists_692 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_caf'45'go'45'mainexists_692 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_caf'45'go'45'mainexists_692 v0 v1 v2 v3 v5
du_caf'45'go'45'mainexists_692 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_caf'45'go'45'mainexists_692 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_tnil_14 -> erased
      MAlonzo.Code.Once.Spec.Module.C_tcons_26 v8 v9 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> coe
                    du_go_732 (coe v0) (coe v2) (coe v13) (coe v14) (coe v8) (coe v12)
                    (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.go
d_go_732 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_732 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 ~v9 v10 ~v11 ~v12 ~v13
  = du_go_732 v0 v1 v2 v3 v4 v8 v10
du_go_732 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_732 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.Compile.du_compileFun'45'aux_184
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1) (coe v0)
              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> let v9
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v1)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                     -> coe
                          du_dispatch_778 (coe v0) (coe v1) (coe v2) (coe v4) (coe v3)
                          (coe v10) (coe v5) (coe v6)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._._.cf0
d_cf0_772 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_234
d_cf0_772 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17
  = du_cf0_772 v2 v3 v7
du_cf0_772 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_234
du_cf0_772 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)) (coe v1)
            (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)) (coe v1)
            (coe v2)))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v0))
-- Once.Adequacy.ModuleComplete._._.fm0
d_fm0_774 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fm0_774 = erased
-- Once.Adequacy.ModuleComplete._._.dispatch
d_dispatch_778 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dispatch_778 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
               v14 ~v15 ~v16 ~v17
  = du_dispatch_778 v0 v1 v2 v3 v4 v5 v12 v14
du_dispatch_778 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dispatch_778 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v8 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v8 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
           -> if coe v9
                then coe
                       seq (coe v10)
                       (case coe v2 of
                          MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v11 v12 v13 v14
                            -> coe
                                 du_mx_794 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v14) erased erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       seq (coe v10)
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             du_caf'45'go'45'mainexists_692 (coe v0) (coe v4)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v1)
                                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v3))
                             (coe v6) (coe v7)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._._._.mx
d_mx_794 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_mx_794 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14
         ~v15 v16 ~v17 ~v18 ~v19 v20 v21 v22
  = du_mx_794 v3 v4 v5 v6 v7 v14 v16 v20 v21 v22
du_mx_794 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_mx_794 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = if coe v7
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                du_caf'45'go'45'mainexists_692 (coe v0) (coe v3)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v1)
                   (coe ("main" :: Data.Text.Text)) (coe v2))
                (coe v5) (coe v6))
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) (coe v9)))
-- Once.Adequacy.ModuleComplete.moduleToIR-sound
d_moduleToIR'45'sound_812 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'sound_812 v0 v1 v2 ~v3
  = du_moduleToIR'45'sound_812 v0 v1 v2
du_moduleToIR'45'sound_812 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'sound_812 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_500
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_182
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> let v7
                           = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v6))
                               (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64) in
                     coe
                       (coe
                          seq (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                du_caf'45'go'45'mains_592
                                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v6))
                                (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64) (coe v1))
                             (coe
                                du_caf'45'go'45'mainexists_692
                                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v6))
                                (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64) (coe v1)
                                (coe v2))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
