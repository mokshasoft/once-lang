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
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
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
d_FunBundle_12 a0 a1 a2 a3 = ()
data T_FunBundle_12
  = C_bnil_20 |
    C_bcons_46 MAlonzo.Code.Once.Type.T_Type_108
               MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               MAlonzo.Code.Once.IR.T_IR_16 T_FunBundle_12
-- Once.Adequacy.FunBundle.compileFunBody-ce
d_compileFunBody'45'ce_72 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'ce_72 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'ce_72 v1 v2 v3 v4 v5 v6
du_compileFunBody'45'ce_72 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'ce_72 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_34
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1308
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
         (coe v5) (coe v4))
-- Once.Adequacy.FunBundle.compileFun-main-aux-ce
d_compileFun'45'main'45'aux'45'ce_116 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'ce_116 ~v0 v1 v2 v3 v4 v5 v6 v7 ~v8
                                      ~v9
  = du_compileFun'45'main'45'aux'45'ce_116 v1 v2 v3 v4 v5 v6 v7
du_compileFun'45'main'45'aux'45'ce_116 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'ce_116 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         du_compileFunBody'45'ce_72 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5))
-- Once.Adequacy.FunBundle.compileFun-aux-ce
d_compileFun'45'aux'45'ce_176 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'ce_176 ~v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'ce_176 v1 v2 v3 v4 v5 v6 v7
du_compileFun'45'aux'45'ce_176 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'ce_176 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             du_compileFun'45'main'45'aux'45'ce_116 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v4))
      else coe
             du_compileFunBody'45'ce_72 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5)
-- Once.Adequacy.FunBundle.compileFun-ce
d_compileFun'45'ce_230 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'ce_230 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_compileFun'45'ce_230 v0 v1 v2 v3 v4
du_compileFun'45'ce_230 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'ce_230 v0 v1 v2 v3 v4
  = coe
      du_compileFun'45'aux'45'ce_176 (coe v2) (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v3)
      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86
         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4))
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.FunBundle.bundle→typed
d_bundle'8594'typed_254 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
d_bundle'8594'typed_254 v0 v1 v2 v3 v4
  = case coe v4 of
      C_bnil_20 -> coe MAlonzo.Code.Once.Adequacy.AcceptSound.C_tnil_132
      C_bcons_46 v8 v9 v10 v11 v12 v13 v17
        -> case coe v2 of
             (:) v18 v19
               -> coe
                    MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                          (coe v3) (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v18)) (coe v8))
                       (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v18)) (coe v8))
                    (d_bundle'8594'typed_254
                       (coe v0) (coe v1) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v18)) (coe v8))
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bundle→compiled
d_bundle'8594'compiled_276 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_230]
d_bundle'8594'compiled_276 ~v0 ~v1 v2 ~v3 v4
  = du_bundle'8594'compiled_276 v2 v4
du_bundle'8594'compiled_276 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_230]
du_bundle'8594'compiled_276 v0 v1
  = case coe v1 of
      C_bnil_20 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_bcons_46 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Compile.C_mkCompiledFun_248
                       (coe
                          MAlonzo.Code.Once.CanonicalName.d_bare_12
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15)) (coe v5)
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             MAlonzo.Code.Once.Compile.d_maybeWrapMain_18
                             (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15)) (coe v5)
                             (coe v10)))
                       (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v15)))
                    (coe du_bundle'8594'compiled_276 (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.CGB
d_CGB_302 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] -> ()
d_CGB_302 = erased
-- Once.Adequacy.FunBundle.caf-go-bundleP
d_caf'45'go'45'bundleP_326 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caf'45'go'45'bundleP_326 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'go'45'bundleP_326 v0 v1 v2 v3
du_caf'45'go'45'bundleP_326 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caf'45'go'45'bundleP_326 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_bnil_20) erased
      (:) v4 v5
        -> coe
             du_cgb'45'rf_342 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_340 (coe v3) (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v4))
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-rf
d_cgb'45'rf_342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'rf_342 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_cgb'45'rf_342 v0 v1 v2 v3 v4 v6
du_cgb'45'rf_342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'rf_342 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_cgb'45'cf_360 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFun_212
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v4) (coe v0)
                (coe v1) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2))
                (coe v6) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-cf
d_cgb'45'cf_360 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'cf_360 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_cgb'45'cf_360 v0 v1 v2 v3 v4 v5 v7
du_cgb'45'cf_360 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'cf_360 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_cgb'45'rec_380 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v7)
             (coe
                MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0) (coe v1)
                (coe v3)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v4)
                   (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2)) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-rec
d_cgb'45'rec_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'rec_380 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
  = du_cgb'45'rec_380 v0 v1 v2 v3 v4 v5 v6 v8
du_cgb'45'rec_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'rec_380 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_bcons_46 v5
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_compileFun'45'ce_230 (coe v0) (coe v1) (coe v4) (coe v5)
                      (coe v2)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         du_compileFun'45'ce_230 (coe v0) (coe v1) (coe v4) (coe v5)
                         (coe v2))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            du_compileFun'45'ce_230 (coe v0) (coe v1) (coe v4) (coe v5)
                            (coe v2)))))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               du_compileFun'45'ce_230 (coe v0) (coe v1) (coe v4) (coe v5)
                               (coe v2))))))
                v6
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_caf'45'go'45'bundleP_326 (coe v0) (coe v1) (coe v3)
                      (coe
                         MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v4)
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v2)) (coe v5)))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.caf-go-bundle
d_caf'45'go'45'bundle_558 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FunBundle_12
d_caf'45'go'45'bundle_558 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'go'45'bundle_558 v0 v1 v2 v3
du_caf'45'go'45'bundle_558 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_FunBundle_12
du_caf'45'go'45'bundle_558 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_caf'45'go'45'bundleP_326 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.FunBundle.bundle→compiled≡compiled
d_bundle'8594'compiled'8801'compiled_584 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bundle'8594'compiled'8801'compiled_584 = erased
-- Once.Adequacy.FunBundle.BMainExists
d_BMainExists_606 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_FunBundle_12 -> ()
d_BMainExists_606 = erased
-- Once.Adequacy.FunBundle.bf-dispatch
d_bf'45'dispatch_618 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bf'45'dispatch_618 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_bf'45'dispatch_618 v2 v3 v4 v5 v6
du_bf'45'dispatch_618 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bf'45'dispatch_618 v0 v1 v2 v3 v4
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
d_bundle'45'find_648 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bundle'45'find_648 ~v0 ~v1 v2 ~v3 v4
  = du_bundle'45'find_648 v2 v4
du_bundle'45'find_648 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bundle'45'find_648 v0 v1
  = case coe v1 of
      C_bnil_20 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_bcons_46 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe
                    du_bf'45'dispatch_618 (coe v10)
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54
                       (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15))
                       (coe ("main" :: Data.Text.Text)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224 (coe v5)
                       (coe d_EffUU_6))
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v15))
                    (coe du_bundle'45'find_648 (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.fa-head
d_fa'45'head_692 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fa'45'head_692 = erased
-- Once.Adequacy.FunBundle.find-agree
d_find'45'agree_888 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'agree_888 = erased
-- Once.Adequacy.FunBundle.bme→me
d_bme'8594'me_916 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
d_bme'8594'me_916 ~v0 ~v1 v2 ~v3 v4 v5
  = du_bme'8594'me_916 v2 v4 v5
du_bme'8594'me_916 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
du_bme'8594'me_916 v0 v1 v2
  = case coe v1 of
      C_bcons_46 v6 v7 v8 v9 v10 v11 v15
        -> case coe v0 of
             (:) v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v18 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v18
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_bme'8594'me_916 (coe v17) (coe v15) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.br-dispatch
d_br'45'dispatch_954 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_br'45'dispatch_954 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12
                     v13 v14 v15
  = du_br'45'dispatch_954 v0 v1 v2 v3 v4 v5 v6 v11 v12 v13 v14 v15
du_br'45'dispatch_954 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_br'45'dispatch_954 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = if coe v11
      then coe
             d_bundle'45'realize_968 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
             (coe v7) (coe v8)
      else (case coe v9 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                -> if coe v12
                     then coe
                            seq (coe v13)
                            (case coe v10 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                 -> if coe v14
                                      then coe
                                             seq (coe v15)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
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
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funName_108
                                                               (coe v5))
                                                            (coe d_EffUU_6))
                                                         (coe v3))
                                                      (coe v0) (coe v1))
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_114
                                                      (coe v5))
                                                   (coe d_EffUU_6) (coe v6)
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                                                         (coe v3) (coe v0) (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Parser.d_funName_108
                                                            (coe v5))
                                                         (coe d_EffUU_6))
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funBody_114
                                                         (coe v5))
                                                      (coe d_EffUU_6))))
                                      else coe
                                             seq (coe v15)
                                             (coe
                                                d_bundle'45'realize_968 (coe v0) (coe v1) (coe v2)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_108
                                                      (coe v5))
                                                   (coe v4))
                                                (coe v7) (coe v8))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v13)
                            (coe
                               d_bundle'45'realize_968 (coe v0) (coe v1) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
                               (coe v7) (coe v8))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-realize
d_bundle'45'realize_968 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'realize_968 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_bcons_46 v9 v10 v11 v12 v13 v14 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  seq (coe v23)
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
                                                    (coe v19))
                                                 (coe d_EffUU_6))
                                              (coe v3))
                                           (coe v0) (coe v1))
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v19))
                                        (coe d_EffUU_6) (coe v10)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                                              (coe v3) (coe v0) (coe v1)
                                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v19))
                                              (coe d_EffUU_6))
                                           (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v19))
                                           (coe d_EffUU_6))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           du_br'45'dispatch_954 (coe v0) (coe v1) (coe v20) (coe v3) (coe v9)
                           (coe v19) (coe v10) (coe v18) (coe v21)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v19))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224 (coe v9)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.realize-agree
d_realize'45'agree_1054 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_realize'45'agree_1054 = erased
-- Once.Adequacy.FunBundle.ra-head
d_ra'45'head_1082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  T_FunBundle_12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ra'45'head_1082 = erased
-- Once.Adequacy.FunBundle.RNode
d_RNode_1184 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_RNode_1184 = erased
-- Once.Adequacy.FunBundle.bundle-realize-node
d_bundle'45'realize'45'node_1218 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'realize'45'node_1218 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_bcons_46 v9 v10 v11 v12 v13 v14 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  seq (coe v23)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v19))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v12)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v13)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           d_brn'45'dispatch_1252 (coe v0) (coe v1) (coe v20) (coe v3)
                           (coe v9) (coe v19) (coe v10) (coe v11) (coe v12) (coe v13) erased
                           (coe v18) (coe v21)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v19))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224 (coe v9)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.brn-dispatch
d_brn'45'dispatch_1252 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_brn'45'dispatch_1252 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                       v13 v14 v15
  = if coe v15
      then coe
             d_bundle'45'realize'45'node_1218 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
             (coe v11) (coe v12)
      else (case coe v13 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                -> if coe v16
                     then coe
                            seq (coe v17)
                            (case coe v14 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                 -> if coe v18
                                      then coe
                                             seq (coe v19)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_114
                                                      (coe v5))
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
                                                                  (coe v10) erased)))))))
                                      else coe
                                             seq (coe v19)
                                             (coe
                                                d_bundle'45'realize'45'node_1218 (coe v0) (coe v1)
                                                (coe v2)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_108
                                                      (coe v5))
                                                   (coe v4))
                                                (coe v11) (coe v12))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v17)
                            (coe
                               d_bundle'45'realize'45'node_1218 (coe v0) (coe v1) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
                               (coe v11) (coe v12))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-find-exists
d_bundle'45'find'45'exists_1362 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_bundle'45'find'45'exists_1362 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6
  = du_bundle'45'find'45'exists_1362 v2 v4
du_bundle'45'find'45'exists_1362 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  T_FunBundle_12 -> AgdaAny
du_bundle'45'find'45'exists_1362 v0 v1
  = case coe v1 of
      C_bcons_46 v5 v6 v7 v8 v9 v10 v14
        -> case coe v0 of
             (:) v15 v16
               -> let v17
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15)))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                               (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v15))
                               (coe ("main" :: Data.Text.Text))) in
                  coe
                    (let v18
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                               (coe v5) (coe d_EffUU_6) in
                     coe
                       (let v19
                              = MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v15) in
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
                                                                             du_bundle'45'find'45'exists_1362
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
                                                                         du_bundle'45'find'45'exists_1362
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
                                                    du_bundle'45'find'45'exists_1362 (coe v16)
                                                    (coe v14))))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.irFun-main-form
d_irFun'45'main'45'form_1504 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
d_irFun'45'main'45'form_1504 = erased
-- Once.Adequacy.FunBundle.MNodeAt
d_MNodeAt_1526 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_MNodeAt_1526 = erased
-- Once.Adequacy.FunBundle.bundle-main-node
d_bundle'45'main'45'node_1562 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_FunBundle_12 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'main'45'node_1562 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_bcons_46 v9 v10 v11 v12 v13 v14 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  seq (coe v23)
                                  (let v24
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                             erased
                                             (\ v24 ->
                                                coe
                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                  (coe ("main" :: Data.Text.Text)))
                                             (coe
                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                (coe ("main" :: Data.Text.Text))
                                                (coe ("main" :: Data.Text.Text))) in
                                   coe
                                     (case coe v24 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                          -> if coe v25
                                               then coe
                                                      seq (coe v26)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v3)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Parser.d_funBody_114
                                                               (coe v19))
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
                                                                        (coe v13)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              erased erased))))))))
                                               else coe
                                                      seq (coe v26)
                                                      (coe
                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           du_bmn'45'dispatch_1600 (coe v0) (coe v1) (coe v20) (coe v3)
                           (coe v9) (coe v19) (coe v10) (coe v11) (coe v12) (coe v13) erased
                           (coe v18) (coe v21)
                           (coe
                              MAlonzo.Code.Data.String.Properties.d__'8799'__54
                              (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v19))
                              (coe ("main" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224 (coe v9)
                              (coe d_EffUU_6))
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bmn-dispatch
d_bmn'45'dispatch_1600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bmn'45'dispatch_1600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 ~v10 v11 ~v12
                       v13 v14 v15 v16 v17
  = du_bmn'45'dispatch_1600
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11 v13 v14 v15 v16 v17
du_bmn'45'dispatch_1600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
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
  T_FunBundle_12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bmn'45'dispatch_1600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15
  = if coe v15
      then coe
             d_bundle'45'main'45'node_1562 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
             (coe v11) (coe v12)
      else (case coe v13 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                -> if coe v16
                     then coe
                            seq (coe v17)
                            (case coe v14 of
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                 -> if coe v18
                                      then coe
                                             seq (coe v19)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funBody_114
                                                      (coe v5))
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
                                                                  (coe v10)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     erased erased))))))))
                                      else coe
                                             seq (coe v19)
                                             (coe
                                                d_bundle'45'main'45'node_1562 (coe v0) (coe v1)
                                                (coe v2)
                                                (coe
                                                   MAlonzo.Code.Once.Compile.d_extendFunCtx_50
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Once.Parser.d_funName_108
                                                      (coe v5))
                                                   (coe v4))
                                                (coe v11) (coe v12))
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v17)
                            (coe
                               d_bundle'45'main'45'node_1562 (coe v0) (coe v1) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v3)
                                  (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v5)) (coe v4))
                               (coe v11) (coe v12))
              _ -> MAlonzo.RTE.mazUnreachableError)
