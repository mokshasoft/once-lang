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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Principal
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Honest
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Soundness
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.FunBundle.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Lang.Type.T_Type_8
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
-- Once.Adequacy.FunBundle.ctxC
d_ctxC_8 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctxC_8 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
      (coe MAlonzo.Code.Once.Compile.d_ctop_406 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_412 (coe v0))
-- Once.Adequacy.FunBundle.FunBundle
d_FunBundle_12 a0 a1 = ()
data T_FunBundle_12
  = C_bnil_16 |
    C_bffi_32 MAlonzo.Code.Once.Lang.Type.T_Type_8
              MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 AgdaAny
              MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
              T_FunBundle_12 |
    C_bcons_66 MAlonzo.Code.Once.Lang.Type.T_Type_8
               MAlonzo.Code.Once.Lang.Context.T_Usage_46
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               MAlonzo.Code.Once.IR.T_IR_16
               MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
               T_FunBundle_12 |
    C_bpoly_86 MAlonzo.Code.Once.Lang.Context.T_Usage_46
               MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
               T_FunBundle_12
-- Once.Adequacy.FunBundle.compileFunBody-ce
d_compileFunBody'45'ce_112 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'ce_112 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'ce_112 v1 v2 v5 v6
du_compileFunBody'45'ce_112 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'ce_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_compileFunBody'45'aux'45'success_36
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6334
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v0) (coe v1))
         (coe v3) (coe v2))
-- Once.Adequacy.FunBundle.compileFun-main-aux-ce
d_compileFun'45'main'45'aux'45'ce_156 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'ce_156 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7
                                      ~v8 ~v9
  = du_compileFun'45'main'45'aux'45'ce_156 v1 v2 v5 v6 v7
du_compileFun'45'main'45'aux'45'ce_156 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'ce_156 v0 v1 v2 v3 v4
  = coe
      seq (coe v4)
      (coe
         du_compileFunBody'45'ce_112 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.FunBundle.compileFun-aux-ce
d_compileFun'45'aux'45'ce_216 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'ce_216 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'ce_216 v1 v2 v5 v6 v7
du_compileFun'45'aux'45'ce_216 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'ce_216 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_compileFun'45'main'45'aux'45'ce_156 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v2))
      else coe
             du_compileFunBody'45'ce_112 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.FunBundle.compileFun-ce
d_compileFun'45'ce_270 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'ce_270 v0 ~v1 v2 v3 v4 ~v5 ~v6
  = du_compileFun'45'ce_270 v0 v2 v3 v4
du_compileFun'45'ce_270 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'ce_270 v0 v1 v2 v3
  = coe
      du_compileFun'45'aux'45'ce_216 (coe v1) (coe v0) (coe v2)
      (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.FunBundle.bundle→typed
d_bundle'8594'typed_290 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> MAlonzo.Code.Once.Lang.Module.T_ModTele_50
d_bundle'8594'typed_290 v0 v1 v2
  = case coe v2 of
      C_bnil_16 -> coe MAlonzo.Code.Once.Lang.Module.C_'91''93'_54
      C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v1 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v18
                      -> coe
                           MAlonzo.Code.Once.Lang.Module.C_ffi_64 v5 v7 v8 v9
                           (d_bundle'8594'typed_290
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_402
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Once.Lang.Module.d_sig_14
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                          (coe v0))))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Module.d_imps_16
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                       (coe v0)))
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_400 (coe v0)))
                              (coe v17) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v6 v7 v8 v9 v10 v11 v15 v19
        -> case coe v1 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v22
                      -> coe
                           MAlonzo.Code.Once.Lang.Module.C_mono_76 v6 v7 v15
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2432
                              (coe d_ctxC_8 (coe v0))
                              (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v22)) (coe v6))
                           (d_bundle'8594'typed_290
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_402
                                 (coe MAlonzo.Code.Once.Compile.d_csig_396 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendDefs_444
                                    (coe
                                       MAlonzo.Code.Once.Lang.Module.d_imps_16
                                       (coe
                                          MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                          (coe v0)))
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v22)) (coe v6))
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_400 (coe v0)))
                              (coe v21) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v6 v7 v8 v9 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v15
                      -> coe
                           MAlonzo.Code.Once.Lang.Module.C_poly_86 v6
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2432
                              (coe d_ctxC_8 (coe v0))
                              (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v15))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                                 (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v15))))
                           (d_bundle'8594'typed_290
                              (coe
                                 MAlonzo.Code.Once.Compile.C_cscope_402
                                 (coe MAlonzo.Code.Once.Compile.d_csig_396 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Module.d_imps_16
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                       (coe MAlonzo.Code.Once.Compile.d_ctop_406 (coe v0)))
                                    (coe MAlonzo.Code.Once.Compile.d_ctele_400 (coe v0))))
                              (coe v14) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bundle→compiled
d_bundle'8594'compiled_340 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_290]
d_bundle'8594'compiled_340 ~v0 v1 v2
  = du_bundle'8594'compiled_340 v1 v2
du_bundle'8594'compiled_340 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> [MAlonzo.Code.Once.Compile.T_CompiledFun_290]
du_bundle'8594'compiled_340 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16 -> coe du_bundle'8594'compiled_340 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v5 v6 v7 v8 v9 v10 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Compile.C_mkCompiledFun_304
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)))
                              (coe v5) (coe v10))
                           (coe du_bundle'8594'compiled_340 (coe v20) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v5 v6 v7 v8 v11
        -> case coe v0 of
             (:) v12 v13 -> coe du_bundle'8594'compiled_340 (coe v13) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.CGB
d_CGB_370 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] -> ()
d_CGB_370 = erased
-- Once.Adequacy.FunBundle.ce-bundleP
d_ce'45'bundleP_386 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'bundleP_386 v0 v1 v2 ~v3 = du_ce'45'bundleP_386 v0 v1 v2
du_ce'45'bundleP_386 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'bundleP_386 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_bnil_16) erased
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v5
               -> coe
                    du_cgb'45'fun_398 (coe v0) (coe v5) (coe v4) (coe v2)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v5))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v5
               -> coe
                    du_cgb'45'poly'45'p_434 (coe v0) (coe v5) (coe v4) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Compile.d_firstChecking_28
                       (coe d_ctxC_8 (coe v0))
                       (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Principal.d_below_10
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-fun
d_cgb'45'fun_398 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'fun_398 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_cgb'45'fun_398 v0 v1 v2 v3 v4
du_cgb'45'fun_398 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'fun_398 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_cgb'45'prim_410 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
      else coe
             du_cgb'45'mono_422 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_360
                (coe MAlonzo.Code.Once.Compile.d_ctop_406 (coe v0))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_412 (coe v0))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)))
-- Once.Adequacy.FunBundle.cgb-prim
d_cgb'45'prim_410 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'prim_410 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'prim_410 v0 v1 v2 v3 v5
du_cgb'45'prim_410 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'prim_410 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_conc_536 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v5))
             (coe MAlonzo.Code.Once.Lang.Type.Honest.d_honest'63'_202 (coe v5))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-mono
d_cgb'45'mono_422 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'mono_422 v0 v1 v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'mono_422 v0 v1 v2 v5
du_cgb'45'mono_422 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'mono_422 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> let v5
                 = MAlonzo.Code.Once.Compile.d_firstChecking_28
                     (coe d_ctxC_8 (coe v0))
                     (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1))
                     (coe MAlonzo.Code.Once.Lang.Principal.d_below_10 (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6 -> erased
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> let v6
                           = MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v4) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> let v8
                                     = coe
                                         MAlonzo.Code.Once.Compile.du_compileFun'45'aux_234
                                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                         (coe MAlonzo.Code.Once.Compile.d_ctop_406 (coe v0))
                                         (coe MAlonzo.Code.Once.Compile.d_cpolys_412 (coe v0))
                                         (coe
                                            MAlonzo.Code.Once.Compile.d_declImps_416
                                            (coe MAlonzo.Code.Once.Compile.d_ctele_400 (coe v0)))
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                         (coe v4)
                                         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1))
                                         (coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                               erased
                                               (\ v8 ->
                                                  coe
                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.d_funName_106
                                                       (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                  (coe
                                                     MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                     (MAlonzo.Code.Once.Parser.d_funName_106
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                     ("main" :: Data.Text.Text))))) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.Compile.d_compileEntries_498
                                                   (coe MAlonzo.Code.Once.IR.C_Heap_8)
                                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.d_extendScope_466
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Parser.d_funName_106
                                                         (coe v1))
                                                      (coe v4))
                                                   (coe v2) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                                -> erased
                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        C_bcons_66 v4
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              du_compileFun'45'ce_270
                                                              (coe
                                                                 MAlonzo.Code.Once.Compile.d_cpolys_412
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Once.Compile.d_ctop_406
                                                                 (coe v0))
                                                              (coe v4) (coe v1)))
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 du_compileFun'45'ce_270
                                                                 (coe
                                                                    MAlonzo.Code.Once.Compile.d_cpolys_412
                                                                    (coe v0))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Compile.d_ctop_406
                                                                    (coe v0))
                                                                 (coe v4) (coe v1))))
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                 (coe
                                                                    du_compileFun'45'ce_270
                                                                    (coe
                                                                       MAlonzo.Code.Once.Compile.d_cpolys_412
                                                                       (coe v0))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Compile.d_ctop_406
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
                                                                       du_compileFun'45'ce_270
                                                                       (coe
                                                                          MAlonzo.Code.Once.Compile.d_cpolys_412
                                                                          (coe v0))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Compile.d_ctop_406
                                                                          (coe v0))
                                                                       (coe v4) (coe v1))))))
                                                        v9 v7
                                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              du_ce'45'bundleP_386
                                                              (coe
                                                                 MAlonzo.Code.Once.Compile.d_extendScope_466
                                                                 (coe v0)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Parser.d_funName_106
                                                                    (coe v1))
                                                                 (coe v4))
                                                              (coe v2) (coe v11))))
                                                     erased
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> erased
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.cgb-poly-p
d_cgb'45'poly'45'p_434 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'poly'45'p_434 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_cgb'45'poly'45'p_434 v0 v1 v2 v3 v4
du_cgb'45'poly'45'p_434 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'poly'45'p_434 v0 v1 v2 v3 v4
  = coe
      seq (coe v4)
      (coe
         du_cgb'45'poly_446 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6334
            (coe d_ctxC_8 (coe v0))
            (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
            (coe
               MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v1)))))
-- Once.Adequacy.FunBundle.cgb-poly
d_cgb'45'poly_446 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cgb'45'poly_446 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7
  = du_cgb'45'poly_446 v0 v1 v2 v3 v5
du_cgb'45'poly_446 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cgb'45'poly_446 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_bpoly_86 v7 v8 v9 v10
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             du_ce'45'bundleP_386
                             (coe MAlonzo.Code.Once.Compile.d_addEntry_482 (coe v0) (coe v1))
                             (coe v2) (coe v3))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          du_ce'45'bundleP_386
                          (coe MAlonzo.Code.Once.Compile.d_addEntry_482 (coe v0) (coe v1))
                          (coe v2) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle._.conc
d_conc_536 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_conc_536 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 ~v11 v12 ~v13 ~v14
  = du_conc_536 v0 v1 v2 v3 v5 v8 v10 v12
du_conc_536 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conc_536 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_bffi_32 v4 v8 v9 v10
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    du_ce'45'bundleP_386
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_extendSig_474 (coe v0)
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                       (coe v4))
                                    (coe v2) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_ce'45'bundleP_386
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendSig_474 (coe v0)
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4))
                                 (coe v2) (coe v3)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.ce-bundle
d_ce'45'bundle_834 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_FunBundle_12
d_ce'45'bundle_834 v0 v1 v2 ~v3 = du_ce'45'bundle_834 v0 v1 v2
du_ce'45'bundle_834 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] -> T_FunBundle_12
du_ce'45'bundle_834 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_ce'45'bundleP_386 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.FunBundle.bundle→compiled≡compiled
d_bundle'8594'compiled'8801'compiled_852 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_290] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bundle'8594'compiled'8801'compiled_852 = erased
-- Once.Adequacy.FunBundle.BMainExists
d_BMainExists_866 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_FunBundle_12 -> ()
d_BMainExists_866 = erased
-- Once.Adequacy.FunBundle.bundle-find
d_bundle'45'find_882 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_bundle'45'find_882 ~v0 v1 v2 = du_bundle'45'find_882 v1 v2
du_bundle'45'find_882 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> Maybe MAlonzo.Code.Once.IR.T_IR_16
du_bundle'45'find_882 v0 v1
  = case coe v1 of
      C_bnil_16 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16 -> coe du_bundle'45'find_882 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v5 v6 v7 v8 v9 v10 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           MAlonzo.Code.Once.Compile.du_findMain'45'here_1000
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe ("main" :: Data.Text.Text))))
                           (coe
                              MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v5)
                              (coe d_EffUU_6))
                           (coe du_bundle'45'find_882 (coe v20) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v5 v6 v7 v8 v11
        -> case coe v0 of
             (:) v12 v13 -> coe du_bundle'45'find_882 (coe v13) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.find-agree
d_find'45'agree_914 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'agree_914 = erased
-- Once.Adequacy.FunBundle.bme→me
d_bme'8594'me_948 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
d_bme'8594'me_948 ~v0 v1 v2 v3 = du_bme'8594'me_948 v1 v2 v3
du_bme'8594'me_948 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> AgdaAny -> AgdaAny
du_bme'8594'me_948 v0 v1 v2
  = case coe v1 of
      C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v0 of
             (:) v16 v17 -> coe du_bme'8594'me_948 (coe v17) (coe v15) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v6 v7 v8 v9 v10 v11 v15 v19
        -> case coe v0 of
             (:) v20 v21
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v22
                      -> case coe v22 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                             -> case coe v24 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                    -> coe
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v23)
                                            (coe v26))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v22
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_bme'8594'me_948 (coe v21) (coe v19) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v6 v7 v8 v9 v12
        -> case coe v0 of
             (:) v13 v14 -> coe du_bme'8594'me_948 (coe v14) (coe v12) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.IsEntry
d_IsEntry_968 :: MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_IsEntry_968 = erased
-- Once.Adequacy.FunBundle.here-call
d_here'45'call_986 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_290 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_here'45'call_986 v0 v1 v2 ~v3 ~v4 v5 v6
  = du_here'45'call_986 v0 v1 v2 v5 v6
du_here'45'call_986 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_290 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_here'45'call_986 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe MAlonzo.Code.Once.Compile.d_cfType_300 (coe v0))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe seq (coe v8) (coe v3 v4)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v6) (coe v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.here-exists
d_here'45'exists_1030 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_here'45'exists_1030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 v10 v11
  = du_here'45'exists_1030 v6 v7 v8 v10 v11
du_here'45'exists_1030 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_here'45'exists_1030 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                       -> coe
                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v0) (coe v9)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3 v4))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v6)
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3 v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bundle-find-call
d_bundle'45'find'45'call_1074 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bundle'45'find'45'call_1074 ~v0 v1 v2 ~v3 ~v4
  = du_bundle'45'find'45'call_1074 v1 v2
du_bundle'45'find'45'call_1074 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bundle'45'find'45'call_1074 v0 v1
  = case coe v1 of
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe du_bundle'45'find'45'call_1074 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v5 v6 v7 v8 v9 v10 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           du_here'45'call_986
                           (coe
                              MAlonzo.Code.Once.Compile.C_mkCompiledFun_304
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)))
                              (coe v5) (coe v10))
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe ("main" :: Data.Text.Text))))
                           (coe
                              MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v5)
                              (coe d_EffUU_6))
                           (\ v22 -> coe du_bundle'45'find'45'call_1074 (coe v20) (coe v18))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v5 v6 v7 v8 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe du_bundle'45'find'45'call_1074 (coe v13) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.bundle-find-exists
d_bundle'45'find'45'exists_1114 ::
  MAlonzo.Code.Once.Compile.T_CScope_388 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_bundle'45'find'45'exists_1114 ~v0 v1 v2 ~v3 ~v4
  = du_bundle'45'find'45'exists_1114 v1 v2
du_bundle'45'find'45'exists_1114 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_FunBundle_12 -> AgdaAny
du_bundle'45'find'45'exists_1114 v0 v1
  = case coe v1 of
      C_bffi_32 v4 v6 v7 v8 v14
        -> case coe v0 of
             (:) v15 v16
               -> coe du_bundle'45'find'45'exists_1114 (coe v16) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bcons_66 v5 v6 v7 v8 v9 v10 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           du_here'45'exists_1030 erased
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe ("main" :: Data.Text.Text))))
                           (coe
                              MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v5)
                              (coe d_EffUU_6))
                           (\ v22 -> coe du_bundle'45'find'45'exists_1114 (coe v20) (coe v18))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bpoly_86 v5 v6 v7 v8 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe du_bundle'45'find'45'exists_1114 (coe v13) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.ProgramNode
d_ProgramNode_1146 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> ()
d_ProgramNode_1146 = erased
-- Once.Adequacy.FunBundle.node-ce
d_node'45'ce_1164 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_node'45'ce_1164 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_node'45'ce_1164 v2 v3 v6
du_node'45'ce_1164 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_node'45'ce_1164 v0 v1 v2
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
                      du_ce'45'bundle_834
                      (coe MAlonzo.Code.Once.Compile.d_emptyCScope_404) (coe v0)
                      (coe v3))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.node-ef
d_node'45'ef_1198 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_node'45'ef_1198 ~v0 ~v1 v2 ~v3 ~v4 = du_node'45'ef_1198 v2
du_node'45'ef_1198 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_node'45'ef_1198 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             du_node'45'ce_1164 (coe v1)
             (coe
                MAlonzo.Code.Once.Compile.d_compileEntries_498
                (coe MAlonzo.Code.Once.IR.C_Heap_8)
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Once.Compile.d_emptyCScope_404) (coe v1))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.FunBundle.program-node
d_program'45'node_1222 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_program'45'node_1222 v0 ~v1 ~v2 = du_program'45'node_1222 v0
du_program'45'node_1222 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_program'45'node_1222 v0
  = coe
      du_node'45'ef_1198
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_632
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
