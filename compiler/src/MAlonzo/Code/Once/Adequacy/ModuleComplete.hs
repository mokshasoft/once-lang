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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ModuleComplete.cong₃
d_cong'8323'_28 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8323'_28 = erased
-- Once.Adequacy.ModuleComplete.compileFunBody-complete
d_compileFunBody'45'complete_48 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6
du_compileFunBody'45'complete_48 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         du_succ_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6338
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe v0) (coe v1))
            (coe v5) (coe v4)))
-- Once.Adequacy.ModuleComplete._.succ
d_succ_78 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_succ_78 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_succ_78 v0 v1 v2 v3 v4 v5 v7
du_succ_78 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_succ_78 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe
                      MAlonzo.Code.Once.Optimize.d_optimize_1248
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)))
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                         (coe (0 :: Integer))
                         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                            (coe v4) (coe v1) (coe v2)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                            (coe (0 :: Integer))
                            (coe
                               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                               (coe
                                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                  (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
                                  (coe v1)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
                               (coe v5) (coe v4)
                               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v8)))))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                         (coe v4) (coe v1) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                         (coe (0 :: Integer))
                         (coe
                            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                            (coe
                               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                               (coe (0 :: Integer))
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                               (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
                               (coe v1)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
                            (coe v5) (coe v4)
                            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v8)))))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.compileFun-complete
d_compileFun'45'complete_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6
du_compileFun'45'complete_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6
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
                          du_compileFunBody'45'complete_48 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_150) (coe v5)
                          (coe v6))
                else coe
                       seq (coe v9)
                       (coe
                          du_compileFunBody'45'complete_48 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v5) (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.scopeOf
d_scopeOf_176 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6
d_scopeOf_176
  = coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
-- Once.Adequacy.ModuleComplete.checkOK-complete
d_checkOK'45'complete_194 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkOK'45'complete_194 = erased
-- Once.Adequacy.ModuleComplete.ce-complete
d_ce'45'complete_204 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'complete_204 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v6 v10 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'complete_204
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v16)) (coe v6))
                                 (coe v15) (coe v13) (coe v3)))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v6 v7 v9 v14 v15 v16
        -> case coe v1 of
             (:) v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v19
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
                                        (coe
                                           MAlonzo.Code.Once.Spec.Name.d_bare_14
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v19)))
                                        (coe v7)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              du_compileFun'45'complete_96
                                              (coe MAlonzo.Code.Once.Compile.d_ctop_450 (coe v0))
                                              (coe MAlonzo.Code.Once.Compile.d_cpolys_456 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Compile.d_declImps_460
                                                 (coe
                                                    MAlonzo.Code.Once.Compile.d_ctele_444 (coe v0)))
                                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v19))
                                              (coe v7)
                                              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v19))
                                              (coe v9))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ce'45'complete_204
                                           (coe
                                              MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v19))
                                              (coe v7))
                                           (coe v18) (coe v16) (coe v21))))
                                  erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v7 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'complete_204
                                 (coe MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0) (coe v13))
                                 (coe v12) (coe v10) (coe v3)))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.FindResult
d_FindResult_300 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> ()
d_FindResult_300 = erased
-- Once.Adequacy.ModuleComplete.ce-find-complete
d_ce'45'find'45'complete_316 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'find'45'complete_316 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v7 v11 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'find'45'complete_316
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) (coe v7))
                                 (coe v16) (coe v14) (coe v3) (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ce'45'find'45'complete_316
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17))
                                          (coe v7))
                                       (coe v16) (coe v14) (coe v3) (coe v4))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ce'45'find'45'complete_316
                                             (coe
                                                MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.d_funName_106 (coe v17))
                                                (coe v7))
                                             (coe v16) (coe v14) (coe v3) (coe v4)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v7 v8 v10 v15 v16 v17
        -> case coe v1 of
             (:) v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v20
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                             -> coe
                                  du_step_462 (coe v0) (coe v20) (coe v8) (coe v19) (coe v10)
                                  (coe v17) (coe v22) (coe v4)
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                     (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v20))
                                     (coe ("main" :: Data.Text.Text)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v8 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'find'45'complete_316
                                 (coe MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0) (coe v14))
                                 (coe v13) (coe v11) (coe v3) (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ce'45'find'45'complete_316
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0)
                                          (coe v14))
                                       (coe v13) (coe v11) (coe v3) (coe v4))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ce'45'find'45'complete_316
                                             (coe
                                                MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0)
                                                (coe v14))
                                             (coe v13) (coe v11) (coe v3) (coe v4)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.cfc
d_cfc_420 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfc_420 v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15
  = du_cfc_420 v0 v1 v3 v5
du_cfc_420 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfc_420 v0 v1 v2 v3
  = coe
      du_compileFun'45'complete_96
      (coe MAlonzo.Code.Once.Compile.d_ctop_450 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_456 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_declImps_460
         (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v0)))
      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2)
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) (coe v3)
-- Once.Adequacy.ModuleComplete._.irFun
d_irFun_422 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_irFun_422 v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
            ~v14 ~v15
  = du_irFun_422 v0 v1 v3 v5
du_irFun_422 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_irFun_422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_cfc_420 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ModuleComplete._.chain
d_chain_426 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain_426 = erased
-- Once.Adequacy.ModuleComplete._.cf0
d_cf0_432 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_298
d_cf0_432 v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
          ~v14 ~v15
  = du_cf0_432 v0 v1 v3 v5
du_cf0_432 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_298
du_cf0_432 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_312
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)))
      (coe v2) (coe du_irFun_422 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.ModuleComplete._.here
d_here_438 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_here_438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18
  = du_here_438
du_here_438 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_here_438 = coe du_found_458
-- Once.Adequacy.ModuleComplete._._.found
d_found_458 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_found_458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
  = du_found_458
du_found_458 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_found_458
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Compile.d_mainCall_1024) erased
-- Once.Adequacy.ModuleComplete._.step
d_step_462 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_462 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
           v14 ~v15 v16 v17
  = du_step_462 v0 v1 v3 v4 v5 v12 v14 v16 v17
du_step_462 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_462 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
        -> coe
             seq (coe v9)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe du_cf0_432 (coe v0) (coe v1) (coe v2) (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ce'45'complete_204
                         (coe
                            MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                         (coe v3) (coe v5) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe du_here_438))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe du_here_438)))))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> case coe v8 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
               -> if coe v10
                    then coe
                           seq (coe v11)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe du_cf0_432 (coe v0) (coe v1) (coe v2) (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ce'45'complete_204
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                          (coe v2))
                                       (coe v3) (coe v5) (coe v6))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe du_here_438))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe du_here_438)))))
                    else coe
                           seq (coe v11)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe du_cf0_432 (coe v0) (coe v1) (coe v2) (coe v4))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ce'45'find'45'complete_316
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                          (coe v2))
                                       (coe v3) (coe v5) (coe v6) (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ce'45'find'45'complete_316
                                          (coe
                                             MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                             (coe v2))
                                          (coe v3) (coe v5) (coe v6) (coe v9))))
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.moduleToIR-complete
d_moduleToIR'45'complete_508 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'complete_508 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_538
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> let v5
                    = d_ce'45'find'45'complete_316
                        (coe MAlonzo.Code.Once.Compile.d_emptyCScope_448) (coe v4) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe
                                 seq (coe v9)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.ce-mains
d_ce'45'mains_556 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_ce'45'mains_556 v0 v1 v2 ~v3 ~v4 = du_ce'45'mains_556 v0 v1 v2
du_ce'45'mains_556 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 -> AgdaAny
du_ce'45'mains_556 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_54
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v5 v9 v10 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v15
                      -> coe
                           du_ce'45'mains_556
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)) (coe v5))
                           (coe v14) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v5 v6 v8 v13 v14 v15
        -> case coe v1 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v18
                      -> coe
                           du_go_642 (coe v0) (coe v18) (coe v6) (coe v17) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Compile.du_compileFun_280
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (coe MAlonzo.Code.Once.Compile.d_ctop_450 (coe v0))
                              (coe MAlonzo.Code.Once.Compile.d_cpolys_456 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.Compile.d_declImps_460
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v0)))
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18)) (coe v6)
                              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v18)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v6 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v12
                      -> coe
                           du_ce'45'mains_556
                           (coe MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0) (coe v12))
                           (coe v11) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.eq′
d_eq'8242'_634 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'8242'_634 = erased
-- Once.Adequacy.ModuleComplete._.go
d_go_642 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_642 v0 v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
         ~v14 v15 ~v16
  = du_go_642 v0 v1 v3 v4 v12 v15
du_go_642 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_642 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe
                du_ce'45'mains_556
                (coe
                   MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.ce-mainexists
d_ce'45'mainexists_668 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_ce'45'mainexists_668 v0 v1 v2 ~v3 v4 ~v5 ~v6
  = du_ce'45'mainexists_668 v0 v1 v2 v4
du_ce'45'mainexists_668 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_ce'45'mainexists_668 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_54 -> erased
      MAlonzo.Code.Once.Lang.Module.C_ffi_64 v6 v10 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v16
                      -> coe
                           du_ce'45'mainexists_668
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendSig_496 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v16)) (coe v6))
                           (coe v15) (coe v13) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_78 v6 v7 v9 v14 v15 v16
        -> case coe v1 of
             (:) v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v19
                      -> coe
                           du_go_774 (coe v0) (coe v19) (coe v7) (coe v18) (coe v16) (coe v3)
                           (coe
                              MAlonzo.Code.Once.Compile.du_compileFun_280
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (coe MAlonzo.Code.Once.Compile.d_ctop_450 (coe v0))
                              (coe MAlonzo.Code.Once.Compile.d_cpolys_456 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.Compile.d_declImps_460
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_444 (coe v0)))
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v19)) (coe v7)
                              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v19)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_88 v7 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v13
                      -> coe
                           du_ce'45'mainexists_668
                           (coe MAlonzo.Code.Once.Compile.d_addEntry_504 (coe v0) (coe v13))
                           (coe v12) (coe v10) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.eq′
d_eq'8242'_766 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'8242'_766 = erased
-- Once.Adequacy.ModuleComplete._.go
d_go_774 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_774 v0 v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13 v14
         ~v15 ~v16 v17 ~v18
  = du_go_774 v0 v1 v3 v4 v12 v14 v17
du_go_774 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_774 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_decide_788 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                (coe ("main" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._._.decide
d_decide_788 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_298] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_decide_788 v0 v1 ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 ~v13
             v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_decide_788 v0 v1 v3 v4 v12 v14 v19
du_decide_788 ::
  MAlonzo.Code.Once.Compile.T_CScope_432 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_decide_788 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then case coe v8 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          du_ce'45'mainexists_668
                          (coe
                             MAlonzo.Code.Once.Compile.d_extendScope_488 (coe v0)
                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                          (coe v3) (coe v4) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.moduleToIR-sound
d_moduleToIR'45'sound_820 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'sound_820 v0 v1 v2 ~v3
  = du_moduleToIR'45'sound_820 v0 v1 v2
du_moduleToIR'45'sound_820 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_moduleToIR'45'sound_820 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_538
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> let v5
                    = MAlonzo.Code.Once.Compile.d_compileEntries_520
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                        (coe MAlonzo.Code.Once.Compile.d_emptyCScope_448) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_ce'45'mains_556
                             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_448) (coe v4)
                             (coe v1))
                          (coe
                             du_ce'45'mainexists_668
                             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_448) (coe v4) (coe v1)
                             (coe v2))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
