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
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Completeness
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ModuleComplete.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Type.T_Type_108
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
-- Once.Adequacy.ModuleComplete.compileFunBody-complete
d_compileFunBody'45'complete_24 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'complete_24 v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_compileFunBody'45'complete_24 v0 v1 v2 v3 v4 v5 v7
du_compileFunBody'45'complete_24 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'complete_24 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_124
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v4)
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe
            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3000
            (coe (0 :: Integer))
            (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v4)
            (coe v1)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
               (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
               (coe v0))
            (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_6962
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
                  (coe v5) (coe v4) (coe v6)))))
      erased
-- Once.Adequacy.ModuleComplete.compileFun-complete
d_compileFun'45'complete_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'complete_64 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8
  = du_compileFun'45'complete_64 v0 v1 v2 v3 v4 v5 v8
du_compileFun'45'complete_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'complete_64 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v3))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          du_compileFunBody'45'complete_24 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe d_EffUU_6) (coe v5) (coe v6))
                else coe
                       seq (coe v9)
                       (coe
                          du_compileFunBody'45'complete_24 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v5) (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.AllMainEffUU
d_AllMainEffUU_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 -> ()
d_AllMainEffUU_152 = erased
-- Once.Adequacy.ModuleComplete.MainExists
d_MainExists_168 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 -> ()
d_MainExists_168 = erased
-- Once.Adequacy.ModuleComplete.caf-go-complete
d_caf'45'go'45'complete_188 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'complete_188 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tnil_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v9 v10 v12 v13
        -> case coe v2 of
             (:) v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
                                 (coe
                                    MAlonzo.Code.Once.CanonicalName.d_bare_12
                                    (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                       (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_compileFun'45'complete_64 (coe v3) (coe v0) (coe v1)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                                             (coe v9)
                                             (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14))
                                             (coe v12)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                                       (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_compileFun'45'complete_64 (coe v3) (coe v0) (coe v1)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                                             (coe v9)
                                             (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14))
                                             (coe v12)))))
                                 (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v14)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    d_caf'45'go'45'complete_188 (coe v0) (coe v1) (coe v15)
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                       (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                                       (coe v9))
                                    (coe v13) (coe v17))))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.findMain-main-or-skip
d_findMain'45'main'45'or'45'skip_236 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findMain'45'main'45'or'45'skip_236 v0 v1 ~v2 v3 v4
  = du_findMain'45'main'45'or'45'skip_236 v0 v1 v3 v4
du_findMain'45'main'45'or'45'skip_236 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_findMain'45'main'45'or'45'skip_236 v0 v1 v2 v3
  = if coe v1
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8 (coe v0)) erased
-- Once.Adequacy.ModuleComplete.FindResult
d_FindResult_262 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_FindResult_262 = erased
-- Once.Adequacy.ModuleComplete.caf-go-find-complete
d_caf'45'go'45'find'45'complete_286 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'find'45'complete_286 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v10 v11 v13 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                      -> case coe v6 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                    -> case coe v15 of
                                         MAlonzo.Code.Once.Parser.C_mkFunInfo_118 v22 v23 v24 v25 v26
                                           -> case coe v21 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                  -> let v29
                                                           = coe
                                                               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_124
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                               (coe d_EffUU_6)
                                                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3000
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                  (coe d_EffUU_6) (coe v0)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           ("main"
                                                                            ::
                                                                            Data.Text.Text))
                                                                        (coe d_EffUU_6))
                                                                     (coe v3))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           ("main"
                                                                            ::
                                                                            Data.Text.Text))
                                                                        (coe d_EffUU_6))
                                                                     (coe v3))
                                                                  (coe (0 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Completeness.du_check'45'complete_6962
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                                                                           (coe v3) (coe v0)
                                                                           (coe v1)
                                                                           (coe
                                                                              ("main"
                                                                               ::
                                                                               Data.Text.Text))
                                                                           (coe d_EffUU_6))
                                                                        (coe v25) (coe d_EffUU_6)
                                                                        (coe v13)))) in
                                                     coe
                                                       (let v30
                                                              = d_caf'45'go'45'complete_188
                                                                  (coe v0) (coe v1) (coe v16)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                                     (coe v3)
                                                                     (coe
                                                                        ("main" :: Data.Text.Text))
                                                                     (coe d_EffUU_6))
                                                                  (coe v14) (coe v18) in
                                                        coe
                                                          (case coe v30 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
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
                                                                             (coe v29))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                                                       (coe v31))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8
                                                                          (coe v29))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased erased))
                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                             -> let v20
                                      = d_caf'45'go'45'find'45'complete_286
                                          (coe v0) (coe v1) (coe v16)
                                          (coe
                                             MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15))
                                             (coe v10))
                                          (coe v14) (coe v18) (coe v19) in
                                coe
                                  (let v21 = MAlonzo.Code.Once.Parser.d_funName_108 (coe v15) in
                                   coe
                                     (let v22
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v22 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.d_funName_108
                                                        (coe v15)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                   (coe
                                                      MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                      (MAlonzo.Code.Once.Parser.d_funName_108
                                                         (coe v15)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                      ("main" :: Data.Text.Text))) in
                                      coe
                                        (let v23
                                               = MAlonzo.Code.Once.Parser.d_funBody_114 (coe v15) in
                                         coe
                                           (case coe v22 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                -> if coe v24
                                                     then let v26
                                                                = seq
                                                                    (coe v25)
                                                                    (coe
                                                                       du_compileFunBody'45'complete_24
                                                                       (coe v3) (coe v0) (coe v1)
                                                                       (coe v21) (coe d_EffUU_6)
                                                                       (coe v23) (coe v13)) in
                                                          coe
                                                            (case coe v26 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                 -> case coe v20 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                        -> case coe v30 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                               -> coe
                                                                                    seq (coe v32)
                                                                                    (coe
                                                                                       du_result_462
                                                                                       (coe v15)
                                                                                       (coe v10)
                                                                                       (coe v27)
                                                                                       (coe v29)
                                                                                       (coe v31))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     else (let v26
                                                                 = seq
                                                                     (coe v25)
                                                                     (coe
                                                                        du_compileFunBody'45'complete_24
                                                                        (coe v3) (coe v0) (coe v1)
                                                                        (coe v21) (coe v10)
                                                                        (coe v23) (coe v13)) in
                                                           coe
                                                             (case coe v26 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                                  -> case coe v20 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                         -> case coe v30 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                                -> coe
                                                                                     seq (coe v32)
                                                                                     (coe
                                                                                        du_result_462
                                                                                        (coe v15)
                                                                                        (coe v10)
                                                                                        (coe v27)
                                                                                        (coe v29)
                                                                                        (coe v31))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.findMain-main-here
d_findMain'45'main'45'here_384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'main'45'here_384 = erased
-- Once.Adequacy.ModuleComplete._.cf0
d_cf0_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_230
d_cf0_458 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cf0_458 v3 v5 v12
du_cf0_458 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_230
du_cf0_458 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
            (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
            (coe v2)))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v0))
-- Once.Adequacy.ModuleComplete._.ca-eq
d_ca'45'eq_460 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ca'45'eq_460 = erased
-- Once.Adequacy.ModuleComplete._.result
d_result_462 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_result_462 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
             ~v13 v14 v15 ~v16 ~v17 ~v18
  = du_result_462 v3 v5 v12 v14 v15
du_result_462 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_result_462 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v5 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                 (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0))
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then coe
                       seq (coe v7)
                       (case coe v0 of
                          MAlonzo.Code.Once.Parser.C_mkFunInfo_118 v8 v9 v10 v11 v12
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
                                       (coe
                                          MAlonzo.Code.Once.CanonicalName.d_bare_12
                                          (coe ("main" :: Data.Text.Text)))
                                       (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                       (coe MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8 (coe v2))
                                       (coe v12))
                                    (coe v3))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          du_findMain'45'main'45'or'45'skip_236 (coe v2) (coe v12)
                                          (coe v4) erased))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_findMain'45'main'45'or'45'skip_236 (coe v2)
                                             (coe v12) (coe v4) erased))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe du_cf0_458 (coe v0) (coe v1) (coe v2)) (coe v3))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.ModuleMainEffUU-ef
d_ModuleMainEffUU'45'ef_480 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> ()
d_ModuleMainEffUU'45'ef_480 = erased
-- Once.Adequacy.ModuleComplete.ModuleMainExists-ef
d_ModuleMainExists'45'ef_490 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> ()
d_ModuleMainExists'45'ef_490 = erased
-- Once.Adequacy.ModuleComplete.HasValidMain-decl
d_HasValidMain'45'decl_498 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> AgdaAny -> ()
d_HasValidMain'45'decl_498 = erased
-- Once.Adequacy.ModuleComplete.moduleToIR-complete
d_moduleToIR'45'complete_510 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'complete_510 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> let v5
                 = MAlonzo.Code.Once.Parser.d_guardDistinct_526
                     (coe
                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                        (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> let v9
                                  = d_caf'45'go'45'find'45'complete_286
                                      (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v8))
                                      (coe
                                         MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                         (coe
                                            MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                            (coe v0)))
                                      (coe v7) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
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
d_mainRealized'45'go_572 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized'45'go_572 v0 v1 v2 v3 v4 v5
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
                                        MAlonzo.Code.Once.Denotation.Realize.d_realize_20
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
                                                 (coe d_EffUU_6))
                                              (coe v3))
                                           (coe v0) (coe v1))
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14))
                                        (coe d_EffUU_6) (coe v10) (coe v12)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                      -> coe
                           d_mrg'45'dispatch_598 (coe v0) (coe v1)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                           (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v14)) (coe v15)
                           (coe v3) (coe v9) (coe v10) (coe v12) (coe v13) (coe v16)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v14))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224 (coe v9)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mrg-dispatch
d_mrg'45'dispatch_598 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mrg'45'dispatch_598 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
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
                                               d_mainRealized'45'go_572 (coe v0) (coe v1) (coe v4)
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                  (coe v5) (coe v2) (coe v6))
                                               (coe v9) (coe v10)
                                        else coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Realize.d_realize_20
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
                                                           (coe v2) (coe d_EffUU_6))
                                                        (coe v5))
                                                     (coe v0) (coe v1))
                                                  (coe v3) (coe d_EffUU_6) (coe v7) (coe v8)))
                              else coe
                                     seq (coe v17)
                                     (coe
                                        d_mainRealized'45'go_572 (coe v0) (coe v1) (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                                           (coe v2) (coe v6))
                                        (coe v9) (coe v10))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v15)
                    (coe
                       d_mainRealized'45'go_572 (coe v0) (coe v1) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5) (coe v2)
                          (coe v6))
                       (coe v9) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mainRealized-ef
d_mainRealized'45'ef_654 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized'45'ef_654 v0 v1 v2 ~v3 v4
  = du_mainRealized'45'ef_654 v0 v1 v2 v4
du_mainRealized'45'ef_654 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mainRealized'45'ef_654 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    d_mainRealized'45'go_572
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v6))
                    (coe
                       MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                    (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) (coe v2)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.mainRealized
d_mainRealized_674 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainRealized_674 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             du_mainRealized'45'ef_654 (coe v0)
             (coe
                MAlonzo.Code.Once.Parser.d_extractFunctions_540
                (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                (coe v0))
             (coe v1) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.caf-go-mains
d_caf'45'go'45'mains_696 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_caf'45'go'45'mains_696 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_caf'45'go'45'mains_696 v0 v1 v2 v3 v4
du_caf'45'go'45'mains_696 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny
du_caf'45'go'45'mains_696 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tnil_132
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9 v11 v12
        -> case coe v2 of
             (:) v13 v14
               -> coe
                    du_go_730 (coe v0) (coe v1) (coe v3) (coe v13) (coe v14) (coe v8)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.go
d_go_730 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_730 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_go_730 v0 v1 v2 v3 v4 v5 v9
du_go_730 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_730 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Compile.d_compileFun'45'aux_174
              (coe MAlonzo.Code.Once.IR.C_Heap_8)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2) (coe v0)
              (coe v1) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
              (coe v5) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> let v9
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1)
                        (coe v4)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v2)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v5)) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             du_caf'45'go'45'mains_696 (coe v0) (coe v1) (coe v4)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v2)
                                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v5))
                             (coe v6))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.findMain-skip-prim
d_findMain'45'skip'45'prim_776 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_230 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_findMain'45'skip'45'prim_776 = erased
-- Once.Adequacy.ModuleComplete.caf-go-mainexists
d_caf'45'go'45'mainexists_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_caf'45'go'45'mainexists_802 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_caf'45'go'45'mainexists_802 v0 v1 v2 v3 v4 v6
du_caf'45'go'45'mainexists_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_caf'45'go'45'mainexists_802 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tnil_132 -> erased
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v9 v10 v12 v13
        -> case coe v2 of
             (:) v14 v15
               -> coe
                    du_go_846 (coe v0) (coe v1) (coe v3) (coe v14) (coe v15) (coe v9)
                    (coe v13) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.go
d_go_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_846 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 ~v13 ~v14
  = du_go_846 v0 v1 v2 v3 v4 v5 v9 v11
du_go_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_846 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = MAlonzo.Code.Once.Compile.d_compileFun'45'aux_174
              (coe MAlonzo.Code.Once.IR.C_Heap_8)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v2) (coe v0)
              (coe v1) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
              (coe v5) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v8 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> let v10
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1)
                        (coe v4)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v2)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v5)) in
              coe
                (case coe v10 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                     -> coe
                          du_dispatch_892 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                          (coe v4) (coe v11) (coe v6) (coe v7)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._._.cf0
d_cf0_886 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_230
d_cf0_886 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16 ~v17 ~v18
  = du_cf0_886 v3 v4 v8
du_cf0_886 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_230
du_cf0_886 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
            (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
            (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v0)) (coe v1)
            (coe v2)))
      (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v0))
-- Once.Adequacy.ModuleComplete._._.fm0
d_fm0_888 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fm0_888 = erased
-- Once.Adequacy.ModuleComplete._._.dispatch
d_dispatch_892 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_dispatch_892 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
               ~v14 v15 ~v16 ~v17 ~v18
  = du_dispatch_892 v0 v1 v2 v3 v4 v5 v6 v13 v15
du_dispatch_892 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_dispatch_892 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v9 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                 (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v9 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
           -> if coe v10
                then coe
                       seq (coe v11)
                       (case coe v3 of
                          MAlonzo.Code.Once.Parser.C_mkFunInfo_118 v12 v13 v14 v15 v16
                            -> coe
                                 du_mx_908 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8) (coe v16) erased erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else coe
                       seq (coe v11)
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe
                             du_caf'45'go'45'mainexists_802 (coe v0) (coe v1) (coe v5)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v2)
                                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v4))
                             (coe v7) (coe v8)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._._._.mx
d_mx_908 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_mx_908 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 ~v13 ~v14
         ~v15 v16 ~v17 v18 ~v19 ~v20 ~v21 v22 v23 v24
  = du_mx_908 v4 v5 v6 v7 v8 v9 v16 v18 v22 v23 v24
du_mx_908 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_mx_908 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = if coe v8
      then coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                du_caf'45'go'45'mainexists_802 (coe v0) (coe v1) (coe v4)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v2)
                   (coe ("main" :: Data.Text.Text)) (coe v3))
                (coe v6) (coe v7))
      else coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10)))
-- Once.Adequacy.ModuleComplete.moduleToIR-sound
d_moduleToIR'45'sound_926 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'sound_926 v0 v1 v2 ~v3
  = du_moduleToIR'45'sound_926 v0 v1 v2
du_moduleToIR'45'sound_926 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'sound_926 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_526
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> let v7
                           = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v6))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                  (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                               (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) in
                     coe
                       (coe
                          seq (coe v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                du_caf'45'go'45'mains_696
                                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                                (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) (coe v1))
                             (coe
                                du_caf'45'go'45'mainexists_802
                                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v6))
                                (coe
                                   MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                   (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                                (coe v5) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) (coe v1)
                                (coe v2))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
