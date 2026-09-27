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

module MAlonzo.Code.Once.Adequacy.FunBundle where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.Soundness
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.FunBundle.EffUU
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
-- Once.Adequacy.FunBundle.FunBundle
d_FunBundle_10 a0 a1 a2 = ()
data T_FunBundle_10
  = C_bnil_16 |
    C_bcons_42 MAlonzo.Code.Once.Type.T_Type_108
               MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               MAlonzo.Code.Once.IR.T_IR_16 T_FunBundle_10
-- Once.Adequacy.FunBundle.compileFunBody-ce
d_compileFunBody'45'ce_66 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'ce_66 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_compileFunBody'45'ce_66 v1 v2 v3 v4 v5
du_compileFunBody'45'ce_66 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'ce_66 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1360
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4) (coe v3))
-- Once.Adequacy.FunBundle.compileFun-main-aux-ce
d_compileFun'45'main'45'aux'45'ce_106 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'ce_106 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'main'45'aux'45'ce_106 v1 v2 v3 v4 v5 v6
du_compileFun'45'main'45'aux'45'ce_106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'ce_106 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (coe
         du_compileFunBody'45'ce_66 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Once.Adequacy.FunBundle.compileFun-aux-ce
d_compileFun'45'aux'45'ce_160 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'ce_160 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'aux'45'ce_160 v1 v2 v3 v4 v5 v6
du_compileFun'45'aux'45'ce_160 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'ce_160 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             du_compileFun'45'main'45'aux'45'ce_106 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v3))
      else coe
             du_compileFunBody'45'ce_66 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4)
-- Once.Adequacy.FunBundle.compileFun-ce
d_compileFun'45'ce_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'ce_208 v0 v1 v2 v3 ~v4 ~v5
  = du_compileFun'45'ce_208 v0 v1 v2 v3
du_compileFun'45'ce_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'ce_208 v0 v1 v2 v3
  = coe
      du_compileFun'45'aux'45'ce_160 (coe v1) (coe v0)
      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v2)
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.FunBundle.bundle→typed
d_bundle'8594'typed_228 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
d_bundle'8594'typed_228 v0 v1 v2 v3
  = case coe v3 of
      C_bnil_16 -> coe MAlonzo.Code.Once.Spec.Module.C_tnil_14
      C_bcons_42 v7 v8 v9 v10 v11 v12 v16
        -> case coe v1 of
             (:) v17 v18
               -> coe
                    MAlonzo.Code.Once.Spec.Module.C_tcons_26 v7 v8
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                          (coe v2) (coe v0)
                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) (coe v7))
                       (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v17)) (coe v7))
                    (d_bundle'8594'typed_228
                       (coe v0) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) (coe v7))
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bundle→compiled
d_bundle'8594'compiled_248 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_234]
d_bundle'8594'compiled_248 ~v0 v1 ~v2 v3
  = du_bundle'8594'compiled_248 v1 v3
du_bundle'8594'compiled_248 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_10 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_234]
du_bundle'8594'compiled_248 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_bcons_42 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                       (coe
                          MAlonzo.Code.Once.CanonicalName.d_bare_12
                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)) (coe v5)
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)) (coe v5)
                             (coe v10)))
                       (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v15)))
                    (coe du_bundle'8594'compiled_248 (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.CGB
d_CGB_272 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] -> ()
d_CGB_272 = erased
-- Once.Adequacy.FunBundle.caf-go-bundleP
d_caf'45'go'45'bundleP_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'bundleP_292 v0 v1 v2 ~v3 ~v4
  = du_caf'45'go'45'bundleP_292 v0 v1 v2
du_caf'45'go'45'bundleP_292 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'bundleP_292 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_bnil_16) erased
      (:) v3 v4
        -> coe
             du_cgb'45'rf_306 (coe v0) (coe v3) (coe v4) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_344 (coe v2) (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-rf
d_cgb'45'rf_306 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'rf_306 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'rf_306 v0 v1 v2 v3 v5
du_cgb'45'rf_306 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'rf_306 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_cgb'45'cf_322 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe
                MAlonzo.Code.Once.Compile.du_compileFun_218
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v3) (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v5)
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-cf
d_cgb'45'cf_322 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'cf_322 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_cgb'45'cf_322 v0 v1 v2 v3 v4 v6
du_cgb'45'cf_322 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'cf_322 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_cgb'45'rec_340 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe
                MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v3)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-rec
d_cgb'45'rec_340 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'rec_340 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_cgb'45'rec_340 v0 v1 v2 v3 v4 v5 v7
du_cgb'45'rec_340 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'rec_340 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_bcons_42 v4
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_compileFun'45'ce_208 (coe v0) (coe v3) (coe v4) (coe v1)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_compileFun'45'ce_208 (coe v0) (coe v3) (coe v4) (coe v1))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            du_compileFun'45'ce_208 (coe v0) (coe v3) (coe v4) (coe v1)))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               du_compileFun'45'ce_208 (coe v0) (coe v3) (coe v4) (coe v1))))))
                v5
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_caf'45'go'45'bundleP_292 (coe v0) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v3)
                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4)))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.caf-go-bundle
d_caf'45'go'45'bundle_500 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FunBundle_10
d_caf'45'go'45'bundle_500 v0 v1 v2 ~v3 ~v4
  = du_caf'45'go'45'bundle_500 v0 v1 v2
du_caf'45'go'45'bundle_500 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_FunBundle_10
du_caf'45'go'45'bundle_500 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_caf'45'go'45'bundleP_292 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.FunBundle.bundle→compiled≡compiled
d_bundle'8594'compiled'8801'compiled_522 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bundle'8594'compiled'8801'compiled_522 = erased
-- Once.Adequacy.FunBundle.BMainExists
d_BMainExists_540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_FunBundle_10 -> ()
d_BMainExists_540 = erased
-- Once.Adequacy.FunBundle.bf-dispatch
d_bf'45'dispatch_552 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bf'45'dispatch_552 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_bf'45'dispatch_552 v2 v3 v4 v5 v6
du_bf'45'dispatch_552 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bf'45'dispatch_552 v0 v1 v2 v3 v4
  = if coe v3
      then coe v4
      else (case coe v1 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                -> if coe v5
                     then coe
                            seq (coe v6)
                            (case coe v2 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                 -> if coe v7
                                      then coe
                                             seq (coe v8)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_wrapMainAsEntry_8
                                                   (coe v0)))
                                      else coe seq (coe v8) (coe v4)
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe seq (coe v6) (coe v4)
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-find
d_bundle'45'find_580 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bundle'45'find_580 ~v0 v1 ~v2 v3 = du_bundle'45'find_580 v1 v3
du_bundle'45'find_580 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_10 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bundle'45'find_580 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_bcons_42 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe
                    du_bf'45'dispatch_552 (coe v10)
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54
                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15))
                       (coe ("main" :: Data.Text.Text)))
                    (coe
                       MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v5)
                       (coe d_EffUU_6))
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v15))
                    (coe du_bundle'45'find_580 (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.fa-head
d_fa'45'head_622 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fa'45'head_622 = erased
-- Once.Adequacy.FunBundle.find-agree
d_find'45'agree_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'agree_802 = erased
-- Once.Adequacy.FunBundle.bme→me
d_bme'8594'me_828 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> AgdaAny -> AgdaAny
d_bme'8594'me_828 ~v0 v1 ~v2 v3 v4 = du_bme'8594'me_828 v1 v3 v4
du_bme'8594'me_828 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_10 -> AgdaAny -> AgdaAny
du_bme'8594'me_828 v0 v1 v2
  = case coe v1 of
      C_bcons_42 v6 v7 v8 v9 v10 v11 v15
        -> case coe v0 of
             (:) v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_bme'8594'me_828 (coe v17) (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.br-dispatch
d_br'45'dispatch_864 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FunBundle_10 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_br'45'dispatch_864 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
                     v13 v14
  = du_br'45'dispatch_864 v0 v1 v2 v3 v4 v5 v10 v11 v12 v13 v14
du_br'45'dispatch_864 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_FunBundle_10 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_br'45'dispatch_864 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = if coe v10
      then coe
             d_bundle'45'realize_876 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
             (coe v6) (coe v7)
      else (case coe v8 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                -> if coe v11
                     then coe
                            seq (coe v12)
                            (case coe v9 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                 -> if coe v13
                                      then coe
                                             seq (coe v14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
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
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funName_106
                                                               (coe v4))
                                                            (coe d_EffUU_6))
                                                         (coe v2))
                                                      (coe v0))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_110
                                                      (coe v4))
                                                   (coe d_EffUU_6) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                                                         (coe v2) (coe v0)
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.d_funName_106
                                                            (coe v4))
                                                         (coe d_EffUU_6))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funBody_110
                                                         (coe v4))
                                                      (coe d_EffUU_6))))
                                      else coe
                                             seq (coe v14)
                                             (coe
                                                d_bundle'45'realize_876 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                   (coe v2)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_106
                                                      (coe v4))
                                                   (coe v3))
                                                (coe v6) (coe v7))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v12)
                            (coe
                               d_bundle'45'realize_876 (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
                               (coe v6) (coe v7))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-realize
d_bundle'45'realize_876 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'realize_876 v0 v1 v2 v3 v4
  = case coe v3 of
      C_bcons_42 v8 v9 v10 v11 v12 v13 v17
        -> case coe v1 of
             (:) v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> case coe v20 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                             -> coe
                                  seq (coe v22)
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
                                                    (coe v18))
                                                 (coe d_EffUU_6))
                                              (coe v2))
                                           (coe v0))
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v18))
                                        (coe d_EffUU_6) (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                                              (coe v2) (coe v0)
                                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                                              (coe d_EffUU_6))
                                           (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v18))
                                           (coe d_EffUU_6))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           du_br'45'dispatch_864 (coe v0) (coe v19) (coe v2) (coe v8)
                           (coe v18) (coe v9) (coe v17) (coe v20)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v8)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.realize-agree
d_realize'45'agree_956 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_realize'45'agree_956 = erased
-- Once.Adequacy.FunBundle.ra-head
d_ra'45'head_982 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FunBundle_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ra'45'head_982 = erased
-- Once.Adequacy.FunBundle.RNode
d_RNode_1082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_RNode_1082 = erased
-- Once.Adequacy.FunBundle.bundle-realize-node
d_bundle'45'realize'45'node_1112 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'realize'45'node_1112 v0 v1 v2 v3 v4
  = case coe v3 of
      C_bcons_42 v8 v9 v10 v11 v12 v13 v17
        -> case coe v1 of
             (:) v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> case coe v20 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                             -> coe
                                  seq (coe v22)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v18))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v12)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           d_brn'45'dispatch_1144 (coe v0) (coe v19) (coe v2) (coe v8)
                           (coe v18) (coe v9) (coe v10) (coe v11) (coe v12) erased (coe v17)
                           (coe v20)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v8)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.brn-dispatch
d_brn'45'dispatch_1144 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FunBundle_10 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_brn'45'dispatch_1144 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14
  = if coe v14
      then coe
             d_bundle'45'realize'45'node_1112 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
             (coe v10) (coe v11)
      else (case coe v12 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                -> if coe v15
                     then coe
                            seq (coe v16)
                            (case coe v13 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                 -> if coe v17
                                      then coe
                                             seq (coe v18)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_110
                                                      (coe v4))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v5)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v7)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v9) erased)))))))
                                      else coe
                                             seq (coe v18)
                                             (coe
                                                d_bundle'45'realize'45'node_1112 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                   (coe v2)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_106
                                                      (coe v4))
                                                   (coe v3))
                                                (coe v10) (coe v11))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v16)
                            (coe
                               d_bundle'45'realize'45'node_1112 (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
                               (coe v10) (coe v11))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-find-exists
d_bundle'45'find'45'exists_1248 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_bundle'45'find'45'exists_1248 ~v0 v1 ~v2 v3 ~v4 ~v5
  = du_bundle'45'find'45'exists_1248 v1 v3
du_bundle'45'find'45'exists_1248 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_10 -> AgdaAny
du_bundle'45'find'45'exists_1248 v0 v1
  = case coe v1 of
      C_bcons_42 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> let v17
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15))
                               (coe ("main" :: Data.Text.Text))) in
                  coe
                    (let v18
                           = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168
                               (coe v5) (coe d_EffUU_6) in
                     coe
                       (let v19
                              = MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v15) in
                        coe
                          (case coe v17 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                               -> if coe v20
                                    then case coe v21 of
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                             -> case coe v18 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                    -> if coe v23
                                                         then coe
                                                                seq (coe v24)
                                                                (if coe v19
                                                                   then coe
                                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                          (coe
                                                                             du_bundle'45'find'45'exists_1248
                                                                             (coe v16) (coe v14))
                                                                   else coe
                                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v22)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                erased erased)))
                                                         else coe
                                                                seq (coe v24)
                                                                (coe
                                                                   seq (coe v19)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                      (coe
                                                                         du_bundle'45'find'45'exists_1248
                                                                         (coe v16) (coe v14))))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    else coe
                                           seq (coe v21)
                                           (coe
                                              seq (coe v19)
                                              (coe
                                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                 (coe
                                                    du_bundle'45'find'45'exists_1248 (coe v16)
                                                    (coe v14))))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.irFun-main-form
d_irFun'45'main'45'form_1388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irFun'45'main'45'form_1388 = erased
-- Once.Adequacy.FunBundle.MNodeAt
d_MNodeAt_1406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_MNodeAt_1406 = erased
-- Once.Adequacy.FunBundle.bundle-main-node
d_bundle'45'main'45'node_1438 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_10 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'main'45'node_1438 v0 v1 v2 v3 v4
  = case coe v3 of
      C_bcons_42 v8 v9 v10 v11 v12 v13 v17
        -> case coe v1 of
             (:) v18 v19
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v20
                      -> case coe v20 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                             -> coe
                                  seq (coe v22)
                                  (let v23
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                             erased
                                             (\ v23 ->
                                                coe
                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                  (coe ("main" :: Data.Text.Text)))
                                             (coe
                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                (coe ("main" :: Data.Text.Text))
                                                (coe ("main" :: Data.Text.Text))) in
                                   coe
                                     (case coe v23 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                          -> if coe v24
                                               then coe
                                                      seq (coe v25)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v2)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funBody_110
                                                               (coe v18))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v9)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v10)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe v11)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe v12)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              erased erased))))))))
                                               else coe
                                                      seq (coe v25)
                                                      (coe
                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v20
                      -> coe
                           du_bmn'45'dispatch_1474 (coe v0) (coe v19) (coe v2) (coe v8)
                           (coe v18) (coe v9) (coe v10) (coe v11) (coe v12) erased (coe v17)
                           (coe v20)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.DecEq.d__'8799'T__168 (coe v8)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bmn-dispatch
d_bmn'45'dispatch_1474 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FunBundle_10 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bmn'45'dispatch_1474 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10 ~v11 v12
                       v13 v14 v15 v16
  = du_bmn'45'dispatch_1474
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10 v12 v13 v14 v15 v16
du_bmn'45'dispatch_1474 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_FunBundle_10 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bmn'45'dispatch_1474 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14
  = if coe v14
      then coe
             d_bundle'45'main'45'node_1438 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
             (coe v10) (coe v11)
      else (case coe v12 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                -> if coe v15
                     then coe
                            seq (coe v16)
                            (case coe v13 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                 -> if coe v17
                                      then coe
                                             seq (coe v18)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_110
                                                      (coe v4))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v5)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v7)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe v9)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     erased erased))))))))
                                      else coe
                                             seq (coe v18)
                                             (coe
                                                d_bundle'45'main'45'node_1438 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_66
                                                   (coe v2)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_106
                                                      (coe v4))
                                                   (coe v3))
                                                (coe v10) (coe v11))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v16)
                            (coe
                               d_bundle'45'main'45'node_1438 (coe v0) (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v2)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v4)) (coe v3))
                               (coe v10) (coe v11))
              _ -> MAlonzo.RTE.mazUnreachableError)
