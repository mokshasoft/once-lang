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

module MAlonzo.Code.Once.Adequacy.MainForm where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.ModuleComplete
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs

-- Once.Adequacy.MainForm.EffUU
d_EffUU_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_EffUU_12 ~v0 = du_EffUU_12
du_EffUU_12 :: MAlonzo.Code.Once.Type.T_Type_112
du_EffUU_12
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
-- Once.Adequacy.MainForm.Payload
d_Payload_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> ()
d_Payload_16 = erased
-- Once.Adequacy.MainForm.Form
d_Form_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Form_44 = erased
-- Once.Adequacy.MainForm.MainNode
d_MainNode_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_MainNode_56 = erased
-- Once.Adequacy.MainForm.build-node
d_build'45'node_102 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_build'45'node_102 ~v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_build'45'node_102 v1 v2 v3
du_build'45'node_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_build'45'node_102 v0 v1 v2
  = coe
      du_node_130 (coe v1) (coe v2) erased
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_caf'45'go'45'bundle_558
         (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v2))
         (coe
            MAlonzo.Code.Once.Compile.d_collectSigEffects_498
            (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
         (coe v1) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48))
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'45'find'45'exists_1362
         (coe v1)
         (coe
            MAlonzo.Code.Once.Adequacy.FunBundle.du_caf'45'go'45'bundle_558
            (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v2))
            (coe
               MAlonzo.Code.Once.Compile.d_collectSigEffects_498
               (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
            (coe v1) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)))
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.d_bundle'45'main'45'node_1562
         (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v2))
         (coe
            MAlonzo.Code.Once.Compile.d_collectSigEffects_498
            (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
         (coe v1) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
         (coe
            MAlonzo.Code.Once.Adequacy.FunBundle.du_caf'45'go'45'bundle_558
            (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v2))
            (coe
               MAlonzo.Code.Once.Compile.d_collectSigEffects_498
               (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
            (coe v1) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48))
         (coe
            MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'45'find'45'exists_1362
            (coe v1)
            (coe
               MAlonzo.Code.Once.Adequacy.FunBundle.du_caf'45'go'45'bundle_558
               (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v2))
               (coe
                  MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                  (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
               (coe v1) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48))))
-- Once.Adequacy.MainForm._.node
d_node_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_node_130 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10 v11 v12
  = du_node_130 v2 v3 v8 v9 v11 v12
du_node_130 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_node_130 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> case coe v13 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                    -> case coe v15 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                           -> case coe v17 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                  -> case coe v19 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                         -> coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v0)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe v1)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v2)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v3)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v4)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v6)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v8)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe v10)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe v12)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                         (coe v14)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                            (coe
                                                                                               v16)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v18)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  erased
                                                                                                  (coe
                                                                                                     v21)))))))))))))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainForm.main-node-of
d_main'45'node'45'of_170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'node'45'of_170 ~v0 v1 ~v2 ~v3
  = du_main'45'node'45'of_170 v1
du_main'45'node'45'of_170 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'node'45'of_170 v0
  = coe
      du_mnf'45'ef_222 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
-- Once.Adequacy.MainForm.mnf-caf
d_mnf'45'caf_182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mnf'45'caf_182 ~v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_mnf'45'caf_182 v1 v3 v4 v5
du_mnf'45'caf_182 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mnf'45'caf_182 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe du_build'45'node_102 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainForm.mnf-ef
d_mnf'45'ef_222 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mnf'45'ef_222 ~v0 v1 ~v2 v3 ~v4 ~v5 = du_mnf'45'ef_222 v1 v3
du_mnf'45'ef_222 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mnf'45'ef_222 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_mnf'45'caf_182 (coe v0) (coe v3) (coe v4)
                    (coe
                       MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                       (coe MAlonzo.Code.Once.IR.C_Heap_8)
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v4))
                       (coe
                          MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                       (coe v3) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainForm.main-ir-form
d_main'45'ir'45'form_256 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'ir'45'form_256 ~v0 v1 ~v2 ~v3
  = du_main'45'ir'45'form_256 v1
du_main'45'ir'45'form_256 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'ir'45'form_256 v0
  = coe du_form_268 (coe v0) (coe du_main'45'node'45'of_170 (coe v0))
-- Once.Adequacy.MainForm._.form
d_form_268 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_form_268 ~v0 v1 ~v2 ~v3 v4 = du_form_268 v1 v4
du_form_268 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_form_268 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                         -> case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                -> case coe v19 of
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                       -> case coe v21 of
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                              -> case coe v23 of
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                     -> case coe
                                                                                               v25 of
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    v16)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_2878
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                                                       (coe
                                                                                                          du_EffUU_12)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Compile.d_buildPolyCtx_270
                                                                                                          (coe
                                                                                                             v4))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                ("main"
                                                                                                                 ::
                                                                                                                 Data.Text.Text))
                                                                                                             (coe
                                                                                                                du_EffUU_12))
                                                                                                          (coe
                                                                                                             v12))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                ("main"
                                                                                                                 ::
                                                                                                                 Data.Text.Text))
                                                                                                             (coe
                                                                                                                du_EffUU_12))
                                                                                                          (coe
                                                                                                             v12))
                                                                                                       (coe
                                                                                                          (0 ::
                                                                                                             Integer))
                                                                                                       (coe
                                                                                                          v18))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          v26)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v12)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Compile.d_buildPolyCtx_270
                                                                                                                (coe
                                                                                                                   v4))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                                                                                                      (coe
                                                                                                                         v0)))
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v14)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         v18)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                         (coe
                                                                                                                            v20)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                            (coe
                                                                                                                               v22)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                               (coe
                                                                                                                                  v24)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                  (coe
                                                                                                                                     v2)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                     (coe
                                                                                                                                        v8)
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                        (coe
                                                                                                                                           v10)
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                           erased
                                                                                                                                           (coe
                                                                                                                                              v27)))))))))))))))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainForm.subst-app
d_subst'45'app_316 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'app_316 = erased
-- Once.Adequacy.MainForm.mainRealized-bundle
d_mainRealized'45'bundle_340 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mainRealized'45'bundle_340 = erased
-- Once.Adequacy.MainForm._.Motive
d_Motive_366 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_Motive_366 = erased
-- Once.Adequacy.MainForm._.F
d_F_376 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_F_376 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_F_376 v1 v10 v11
du_F_376 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_F_376 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Adequacy.ModuleComplete.du_mainRealized'45'ef_654
                    (coe v0) (coe v1) (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainForm._.x
d_x_386 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_x_386 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_x_386 v2 v3
du_x_386 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_x_386 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Adequacy.MainForm._.x'
d_x''_388 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_x''_388 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_x''_388 v2 v3
du_x''_388 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_x''_388 v0 v1 = coe du_x_386 (coe v0) (coe v1)
-- Once.Adequacy.MainForm._.mt'
d_mt''_390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
d_mt''_390 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_mt''_390 v2 v3
du_mt''_390 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
du_mt''_390 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_x''_388 (coe v0) (coe v1))
-- Once.Adequacy.MainForm._.me'
d_me''_392 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> AgdaAny
d_me''_392 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_me''_392 v2 v3
du_me''_392 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_me''_392 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_x''_388 (coe v0) (coe v1)))
