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
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.Soundness
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.FunBundle.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Type.T_Type_108
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
-- Once.Adequacy.FunBundle.ctxC
d_ctxC_8 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctxC_8 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
      (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0))
-- Once.Adequacy.FunBundle.FunBundle
d_FunBundle_12 a0 a1 = ()
data T_FunBundle_12
  = C_bnil_16 |
    C_bffi_32 MAlonzo.Code.Once.Type.T_Type_108
              MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 AgdaAny
              MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 T_FunBundle_12 |
    C_bcons_64 MAlonzo.Code.Once.Type.T_Type_108
               MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               MAlonzo.Code.Once.IR.T_IR_16
               MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 T_FunBundle_12 |
    C_bpoly_82 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               T_FunBundle_12
-- Once.Adequacy.FunBundle.compileFunBody-ce
d_compileFunBody'45'ce_108 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'ce_108 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'ce_108 v1 v2 v5 v6
du_compileFunBody'45'ce_108 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'ce_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_36
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe v0) (coe v1))
         (coe v3) (coe v2))
-- Once.Adequacy.FunBundle.compileFun-main-aux-ce
d_compileFun'45'main'45'aux'45'ce_152 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'ce_152 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7
                                      ~v8 ~v9
  = du_compileFun'45'main'45'aux'45'ce_152 v1 v2 v5 v6 v7
du_compileFun'45'main'45'aux'45'ce_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'ce_152 v0 v1 v2 v3 v4
  = coe
      seq (coe v4)
      (coe
         du_compileFunBody'45'ce_108 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.FunBundle.compileFun-aux-ce
d_compileFun'45'aux'45'ce_212 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'ce_212 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'ce_212 v1 v2 v5 v6 v7
du_compileFun'45'aux'45'ce_212 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'ce_212 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_compileFun'45'main'45'aux'45'ce_152 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v2))
      else coe
             du_compileFunBody'45'ce_108 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.FunBundle.compileFun-ce
d_compileFun'45'ce_266 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'ce_266 v0 ~v1 v2 v3 v4 ~v5 ~v6
  = du_compileFun'45'ce_266 v0 v2 v3 v4
du_compileFun'45'ce_266 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'ce_266 v0 v1 v2 v3
  = coe
      du_compileFun'45'aux'45'ce_212 (coe v1) (coe v0) (coe v2)
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.FunBundle.bundle→typed
d_bundle'8594'typed_286 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_bundle'8594'typed_286 v0 v1 v2
  = case coe v2 of
      C_bnil_16 -> coe MAlonzo.Code.Once.Spec.Module.C_'91''93'_42
      C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v1 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Module.C_ffi_52 v5 v7 v8 v9
                           (d_bundle'8594'typed_286
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_386
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Module.d_imps_12
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                          (coe v0))))
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0)))
                              (coe v17) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_64 v6 v7 v8 v9 v10 v11 v14 v18
        -> case coe v1 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           MAlonzo.Code.Once.Spec.Module.C_mono_64 v6 v7 v14
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2502
                              (coe d_ctxC_8 (coe v0))
                              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v21)) (coe v6))
                           (d_bundle'8594'typed_286
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_386
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21))
                                       (coe v6))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Module.d_imps_12
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                          (coe v0))))
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0)))
                              (coe v20) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_82 v6 v7 v8 v9 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v14
                      -> coe
                           MAlonzo.Code.Once.Spec.Module.C_poly_74 v6
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2502
                              (coe d_ctxC_8 (coe v0))
                              (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v14))
                              (coe
                                 MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v14))))
                           (d_bundle'8594'typed_286
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_386
                                 (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                       (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0)))
                                    (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0))))
                              (coe v13) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.primCF
d_primCF_332 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_232
d_primCF_332 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
      (coe
         MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_978
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe (0 :: Integer)))
         (coe v1)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
            (MAlonzo.Code.Once.CanonicalName.d_bare_12
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)))
            v2))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Once.Adequacy.FunBundle.bundle→compiled
d_bundle'8594'compiled_344 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_232]
d_bundle'8594'compiled_344 ~v0 v1 v2
  = du_bundle'8594'compiled_344 v1 v2
du_bundle'8594'compiled_344 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_232]
du_bundle'8594'compiled_344 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe d_primCF_332 (coe v17) (coe v4) (coe v6))
                           (coe du_bundle'8594'compiled_344 (coe v16) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_64 v5 v6 v7 v8 v9 v10 v13 v17
        -> case coe v0 of
             (:) v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v20
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v20)))
                              (coe v5) (coe v10)
                              (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v20)))
                           (coe du_bundle'8594'compiled_344 (coe v19) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_82 v5 v6 v7 v8 v10
        -> case coe v0 of
             (:) v11 v12 -> coe du_bundle'8594'compiled_344 (coe v12) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.CGB
d_CGB_376 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] -> ()
d_CGB_376 = erased
-- Once.Adequacy.FunBundle.ce-bundleP
d_ce'45'bundleP_392 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'bundleP_392 v0 v1 v2 ~v3 = du_ce'45'bundleP_392 v0 v1 v2
du_ce'45'bundleP_392 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'bundleP_392 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_bnil_16) erased
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v5
               -> coe
                    du_cgb'45'fun_404 (coe v0) (coe v5) (coe v4)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v5))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v5
               -> coe
                    du_cgb'45'poly_440 (coe v0) (coe v5) (coe v4) (coe v2)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
                       (coe d_ctxC_8 (coe v0))
                       (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v5))
                       (coe
                          MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                          (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-fun
d_cgb'45'fun_404 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'fun_404 v0 v1 v2 ~v3 v4 ~v5 ~v6
  = du_cgb'45'fun_404 v0 v1 v2 v4
du_cgb'45'fun_404 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'fun_404 v0 v1 v2 v3
  = if coe v3
      then coe
             du_cgb'45'prim_416 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
      else coe
             du_cgb'45'mono_428 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_342
                (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)))
-- Once.Adequacy.FunBundle.cgb-prim
d_cgb'45'prim_416 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'prim_416 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'prim_416 v0 v1 v2 v5
du_cgb'45'prim_416 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'prim_416 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             du_conc_530 (coe v0) (coe v1) (coe v2) (coe v4)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
             (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_86 (coe v4))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-mono
d_cgb'45'mono_428 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'mono_428 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'mono_428 v0 v1 v2 v5
du_cgb'45'mono_428 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'mono_428 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> let v5
                 = MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v4) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> let v7
                           = coe
                               MAlonzo.Code.Once.Compile.du_compileFun'45'aux_176
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
                               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_declImps_396
                                  (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0)))
                               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4)
                               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v7 ->
                                        coe
                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)))
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                        (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           (MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                           ("main" :: Data.Text.Text))))) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> erased
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                            -> let v9
                                     = MAlonzo.Code.Once.Compile.d_compileEntries_448
                                         (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe
                                            MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v0)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                            (coe v4))
                                         (coe v2) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              C_bcons_64 v4
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    du_compileFun'45'ce_266
                                                    (coe
                                                       MAlonzo.Code.Once.Compile.d_cpolys_392
                                                       (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Once.Compile.d_cimps_382
                                                       (coe v0))
                                                    (coe v4) (coe v1)))
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe
                                                       du_compileFun'45'ce_266
                                                       (coe
                                                          MAlonzo.Code.Once.Compile.d_cpolys_392
                                                          (coe v0))
                                                       (coe
                                                          MAlonzo.Code.Once.Compile.d_cimps_382
                                                          (coe v0))
                                                       (coe v4) (coe v1))))
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          du_compileFun'45'ce_266
                                                          (coe
                                                             MAlonzo.Code.Once.Compile.d_cpolys_392
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Once.Compile.d_cimps_382
                                                             (coe v0))
                                                          (coe v4) (coe v1)))))
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             du_compileFun'45'ce_266
                                                             (coe
                                                                MAlonzo.Code.Once.Compile.d_cpolys_392
                                                                (coe v0))
                                                             (coe
                                                                MAlonzo.Code.Once.Compile.d_cimps_382
                                                                (coe v0))
                                                             (coe v4) (coe v1))))))
                                              v8 v6
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    du_ce'45'bundleP_392
                                                    (coe
                                                       MAlonzo.Code.Once.Compile.d_extendScope_424
                                                       (coe v0)
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_funName_106
                                                          (coe v1))
                                                       (coe v4))
                                                    (coe v2) (coe v10))))
                                           erased
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> erased
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-poly
d_cgb'45'poly_440 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'poly_440 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_cgb'45'poly_440 v0 v1 v2 v3 v4
du_cgb'45'poly_440 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'poly_440 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_bpoly_82 v7 v8 v9 v10
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             du_ce'45'bundleP_392
                             (coe MAlonzo.Code.Once.Compile.d_addEntry_432 (coe v0) (coe v1))
                             (coe v2) (coe v3))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          du_ce'45'bundleP_392
                          (coe MAlonzo.Code.Once.Compile.d_addEntry_432 (coe v0) (coe v1))
                          (coe v2) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle._.conc
d_conc_530 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_conc_530 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 ~v11 v12 ~v13
           ~v14
  = du_conc_530 v0 v1 v2 v5 v8 v10 v12
du_conc_530 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conc_530 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> let v10
                               = MAlonzo.Code.Once.Compile.d_compileEntries_448
                                   (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                   (coe
                                      MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v0)
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                      (coe v3))
                                   (coe v2) in
                         coe
                           (case coe v10 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> erased
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_bffi_32 v3 v7 v8 v9
                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              du_ce'45'bundleP_392
                                              (coe
                                                 MAlonzo.Code.Once.Compile.d_extendScope_424
                                                 (coe v0)
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                                 (coe v3))
                                              (coe v2) (coe v11))))
                                     erased
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.ce-bundle
d_ce'45'bundle_804 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FunBundle_12
d_ce'45'bundle_804 v0 v1 v2 ~v3 = du_ce'45'bundle_804 v0 v1 v2
du_ce'45'bundle_804 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] -> T_FunBundle_12
du_ce'45'bundle_804 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_ce'45'bundleP_392 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.FunBundle.bundle→compiled≡compiled
d_bundle'8594'compiled'8801'compiled_822 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bundle'8594'compiled'8801'compiled_822 = erased
-- Once.Adequacy.FunBundle.BMainExists
d_BMainExists_836 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_FunBundle_12 -> ()
d_BMainExists_836 = erased
-- Once.Adequacy.FunBundle.bundle-find
d_bundle'45'find_852 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bundle'45'find_852 ~v0 v1 v2 = du_bundle'45'find_852 v1 v2
du_bundle'45'find_852 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bundle'45'find_852 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16 -> coe du_bundle'45'find_852 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_64 v5 v6 v7 v8 v9 v10 v13 v17
        -> case coe v0 of
             (:) v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v20
                      -> coe
                           MAlonzo.Code.Once.Compile.du_findMain'45'here_810
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v20))
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v20)))
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe ("main" :: Data.Text.Text))))
                           (coe MAlonzo.Code.Once.Compile.d_isEffUU'63'_792 (coe v5))
                           (coe du_bundle'45'find_852 (coe v19) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_82 v5 v6 v7 v8 v10
        -> case coe v0 of
             (:) v11 v12 -> coe du_bundle'45'find_852 (coe v12) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.find-agree
d_find'45'agree_882 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'agree_882 = erased
-- Once.Adequacy.FunBundle.bme→me
d_bme'8594'me_914 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
d_bme'8594'me_914 ~v0 v1 v2 v3 = du_bme'8594'me_914 v1 v2 v3
du_bme'8594'me_914 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
du_bme'8594'me_914 v0 v1 v2
  = case coe v1 of
      C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v0 of
             (:) v16 v17 -> coe du_bme'8594'me_914 (coe v17) (coe v15) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_64 v6 v7 v8 v9 v10 v11 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> case coe v23 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                    -> coe
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v22)
                                            (coe v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_bme'8594'me_914 (coe v20) (coe v18) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_82 v6 v7 v8 v9 v11
        -> case coe v0 of
             (:) v12 v13 -> coe du_bme'8594'me_914 (coe v13) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.here-call
d_here'45'call_946 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_232 ->
  Bool ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_here'45'call_946 = erased
-- Once.Adequacy.FunBundle.here-exists
d_here'45'exists_998 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FunBundle_12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_here'45'exists_998 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                     v12
  = du_here'45'exists_998 v6 v7 v8 v9 v11 v12
du_here'45'exists_998 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_here'45'exists_998 v0 v1 v2 v3 v4 v5
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4 v5)
      else (case coe v2 of
              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                -> if coe v6
                     then coe
                            seq (coe v7)
                            (case coe v3 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                 -> coe
                                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                            (coe v8)))
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4 v5)
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     else coe
                            seq (coe v7)
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4 v5))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.FunBundle.bundle-find-call
d_bundle'45'find'45'call_1052 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bundle'45'find'45'call_1052 = erased
-- Once.Adequacy.FunBundle.bundle-find-exists
d_bundle'45'find'45'exists_1090 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_bundle'45'find'45'exists_1090 ~v0 v1 v2 ~v3 ~v4
  = du_bundle'45'find'45'exists_1090 v1 v2
du_bundle'45'find'45'exists_1090 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_FunBundle_12 -> AgdaAny
du_bundle'45'find'45'exists_1090 v0 v1
  = case coe v1 of
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe du_bundle'45'find'45'exists_1090 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_64 v5 v6 v7 v8 v9 v10 v13 v17
        -> case coe v0 of
             (:) v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v20
                      -> coe
                           du_here'45'exists_998
                           (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v20))
                           erased
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v20)))
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe ("main" :: Data.Text.Text))))
                           (coe MAlonzo.Code.Once.Compile.d_isEffUU'63'_792 (coe v5))
                           (\ v21 -> coe du_bundle'45'find'45'exists_1090 (coe v19) (coe v17))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_82 v5 v6 v7 v8 v10
        -> case coe v0 of
             (:) v11 v12
               -> coe du_bundle'45'find'45'exists_1090 (coe v12) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.ProgramNode
d_ProgramNode_1120 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> ()
d_ProgramNode_1120 = erased
-- Once.Adequacy.FunBundle.node-ce
d_node'45'ce_1138 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_node'45'ce_1138 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_node'45'ce_1138 v2 v3 v6
du_node'45'ce_1138 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_node'45'ce_1138 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      du_ce'45'bundle_804
                      (coe MAlonzo.Code.Once.Compile.d_emptyCScope_388) (coe v0)
                      (coe v3))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.node-ef
d_node'45'ef_1172 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_node'45'ef_1172 ~v0 ~v1 v2 ~v3 ~v4 = du_node'45'ef_1172 v2
du_node'45'ef_1172 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_node'45'ef_1172 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             du_node'45'ce_1138 (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileEntries_448
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Once.Compile.d_emptyCScope_388) (coe v1))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.program-node
d_program'45'node_1196 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_program'45'node_1196 v0 ~v1 ~v2 = du_program'45'node_1196 v0
du_program'45'node_1196 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_program'45'node_1196 v0
  = coe
      du_node'45'ef_1172
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
