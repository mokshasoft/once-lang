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

module MAlonzo.Code.Once.TypeCheck.Soundness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error

-- Once.TypeCheck.Soundness.sound-RInt
d_sound'45'RInt_20 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RInt_20 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RInt_20
du_sound'45'RInt_20 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RInt_20
  = coe MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
-- Once.TypeCheck.Soundness.sound-RUnit
d_sound'45'RUnit_38 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnit_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RUnit_38
du_sound'45'RUnit_38 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnit_38
  = coe MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
-- Once.TypeCheck.Soundness.sound-RVar-unit
d_sound'45'RVar'45'unit_54 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RVar'45'unit_54
du_sound'45'RVar'45'unit_54 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit_54
  = coe MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
-- Once.TypeCheck.Soundness.InferBundle
d_InferBundle_60 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> ()
d_InferBundle_60 = erased
-- Once.TypeCheck.Soundness.inferBundle
d_inferBundle_72 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferBundle_72 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9992 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.CheckBundle
d_CheckBundle_80 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_CheckBundle_80 = erased
-- Once.TypeCheck.Soundness.checkBundle
d_checkBundle_96 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkBundle_96 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_10006 (coe v0)
         (coe v1) (coe v2))
      erased
-- Once.TypeCheck.Soundness.ViewBundle
d_ViewBundle_104 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> ()
d_ViewBundle_104 = erased
-- Once.TypeCheck.Soundness.viewBundle
d_viewBundle_112 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_112 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.d_classifyAppHeadView_340
         (coe v0))
      erased
-- Once.TypeCheck.Soundness.check-soundV
d_check'45'soundV_130 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_check'45'soundV_130 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'soundV_130 v0 v1 v2
du_check'45'soundV_130 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_check'45'soundV_130 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.infer-soundV
d_infer'45'soundV_218 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'soundV_218 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'soundV_218 v0 v1
du_infer'45'soundV_218 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'soundV_218 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.inferElab-eq-RInt
d_inferElab'45'eq'45'RInt_290 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RInt_290 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RUnit
d_inferElab'45'eq'45'RUnit_298 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RUnit_298 = erased
-- Once.TypeCheck.Soundness.sound-RUnaryOp-neg
d_sound'45'RUnaryOp'45'neg_328 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnaryOp'45'neg_328 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RUnaryOp'45'neg_328 v0 v1
du_sound'45'RUnaryOp'45'neg_328 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnaryOp'45'neg_328 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'neg'45'aux_6330
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RAnnot
d_sound'45'RAnnot_432 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RAnnot_432 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sound'45'RAnnot_432 v0 v1 v2
du_sound'45'RAnnot_432 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RAnnot_432 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2842
              (coe v2)
              (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302 (coe v0)
                 (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RPair
d_sound'45'RPair_560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RPair_560 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sound'45'RPair_560 v0 v1 v2
du_sound'45'RPair_560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RPair_560 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RPair'45'aux_2788
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v1))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LookupBundle
d_LookupBundle_662 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LookupBundle_662 = erased
-- Once.TypeCheck.Soundness.lookupBundle
d_lookupBundle_674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupBundle_674 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupImport_38 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RQualified
d_sound'45'RQualified_696 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RQualified_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RQualified_696
du_sound'45'RQualified_696 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RQualified_696 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Soundness.LocalLookupBundle
d_LocalLookupBundle_708 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LocalLookupBundle_708 = erased
-- Once.TypeCheck.Soundness.localLookupBundle
d_localLookupBundle_720 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_localLookupBundle_720 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupLocal_246 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.UnitDecBundle
d_UnitDecBundle_728 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_UnitDecBundle_728 = erased
-- Once.TypeCheck.Soundness.unitDecBundle
d_unitDecBundle_736 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unitDecBundle_736 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe ("unit" :: Data.Text.Text)))
      erased
-- Once.TypeCheck.Soundness.sound-RVar
d_sound'45'RVar_754 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar_754 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RVar_754 v0 v1
du_sound'45'RVar_754 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar_754 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_4806
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupLocal'45'go_162
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0))
                 (coe v1)
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v0))
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0)))
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupImport_38
                 (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v0))
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-check-RVar-id
d_sound'45'check'45'RVar'45'id_834 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_sound'45'check'45'RVar'45'id_834 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'check'45'RVar'45'id_834 v0 v1
du_sound'45'check'45'RVar'45'id_834 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_sound'45'check'45'RVar'45'id_834 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4844
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                 (coe ("id" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RVar-unit-generic
d_sound'45'RVar'45'unit'45'generic_910 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit'45'generic_910 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'RVar'45'unit'45'generic_910
du_sound'45'RVar'45'unit'45'generic_910 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit'45'generic_910 v0
  = coe du_sound'45'RVar'45'unit_54
-- Once.TypeCheck.Soundness.sound-RBinOp
d_sound'45'RBinOp_956 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RBinOp_956 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'RBinOp_956 v0 v1 v2 v3
du_sound'45'RBinOp_956 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RBinOp_956 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_3060
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LetBodyBundle
d_LetBodyBundle_1072 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> ()
d_LetBodyBundle_1072 = erased
-- Once.TypeCheck.Soundness.letBodyBundle
d_letBodyBundle_1092 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_letBodyBundle_1092 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9992
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.sound-RLet
d_sound'45'RLet_1146 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RLet_1146 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'RLet_1146 v0 v1 v2 v3
du_sound'45'RLet_1146 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RLet_1146 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6348
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.CaseBranchBundle
d_CaseBranchBundle_1262 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> ()
d_CaseBranchBundle_1262 = erased
-- Once.TypeCheck.Soundness.caseBranchBundle
d_caseBranchBundle_1282 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseBranchBundle_1282 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9992
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.TyEqBundle
d_TyEqBundle_1296 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_TyEqBundle_1296 = erased
-- Once.TypeCheck.Soundness.tyEqBundle
d_tyEqBundle_1308 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tyEqBundle_1308 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RDestruct
d_sound'45'RDestruct_1376 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RDestruct_1376 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 ~v13 ~v14
  = du_sound'45'RDestruct_1376 v0 v1 v2 v3 v4 v5
du_sound'45'RDestruct_1376 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RDestruct_1376 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6362
              (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe seq (coe v7) (coe v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LamBodyBundle
d_LamBodyBundle_1524 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_LamBodyBundle_1524 = erased
-- Once.TypeCheck.Soundness.lamBodyBundle
d_lamBodyBundle_1548 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lamBodyBundle_1548 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_10006
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
            (coe v1) (coe v2))
         (coe v3) (coe v4))
      erased
-- Once.TypeCheck.Soundness.LeqBundle
d_LeqBundle_1564 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 -> ()
d_LeqBundle_1564 = erased
-- Once.TypeCheck.Soundness.leqBundle
d_leqBundle_1576 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leqBundle_1576 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1302 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-check-RLam
d_sound'45'check'45'RLam_1612 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_sound'45'check'45'RLam_1612 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
                              ~v10 ~v11
  = du_sound'45'check'45'RLam_1612 v0 v1 v2 v3 v4 v5
du_sound'45'check'45'RLam_1612 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_sound'45'check'45'RLam_1612 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (let v7 = coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34 in
       coe
         (case coe v6 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
              -> case coe v8 of
                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v10 v11 v12 v13
                     -> case coe v10 of
                          MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15 v16
                            -> let v17
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1302
                                         (coe v15) (coe v4) in
                               coe
                                 (case coe v17 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                      -> let v19
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_withUnit_478
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("lambda" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   (coe v7)
                                                   (coe
                                                      (\ v19 ->
                                                         coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112
                                                              (coe v16)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lam_34
                                                                 v15 v11)
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v12))
                                                              (coe v13))
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_686
                                                              v15 v19 v9))) in
                                         coe
                                           (case coe v19 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                -> coe seq (coe v20) (coe v21)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v10
                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Soundness.sound-RApp-id
d_sound'45'RApp'45'id_1752 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'id_1752 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'id_1752 v0 v1
du_sound'45'RApp'45'id_1752 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'id_1752 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                                     (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_id_20) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_282 v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-terminal
d_sound'45'RApp'45'terminal_1856 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'terminal_1856 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'terminal_1856 v0 v1
du_sound'45'RApp'45'terminal_1856 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'terminal_1856 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88
                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56
                                     (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_terminal_72) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_316 v5 v6
                                  v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-fst
d_sound'45'RApp'45'fst_1960 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'fst_1960 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'fst_1960 v0 v1
du_sound'45'RApp'45'fst_1960 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'fst_1960 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2432 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-snd
d_sound'45'RApp'45'snd_2064 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'snd_2064 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'snd_2064 v0 v1
du_sound'45'RApp'45'snd_2064 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'snd_2064 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2508 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-apply
d_sound'45'RApp'45'apply_2168 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'apply_2168 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'apply_2168 v0 v1
du_sound'45'RApp'45'apply_2168 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'apply_2168 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2758 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-generic
d_sound'45'RApp'45'generic_2286 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'generic_2286 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11
  = du_sound'45'RApp'45'generic_2286 v0 v1 v2
du_sound'45'RApp'45'generic_2286 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'generic_2286 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6410
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_classifyAppHeadView_340
                 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-id
d_classifyAppHeadView'45'RVar'45'id_2384 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'id_2384 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-fst
d_classifyAppHeadView'45'RVar'45'fst_2386 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'fst_2386 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-snd
d_classifyAppHeadView'45'RVar'45'snd_2388 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'snd_2388 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-terminal
d_classifyAppHeadView'45'RVar'45'terminal_2390 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'terminal_2390 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-apply
d_classifyAppHeadView'45'RVar'45'apply_2392 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'apply_2392 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inl
d_classifyAppHeadView'45'RVar'45'inl_2394 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inl_2394 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inr
d_classifyAppHeadView'45'RVar'45'inr_2396 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inr_2396 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-initial
d_classifyAppHeadView'45'RVar'45'initial_2398 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'initial_2398 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-curry
d_classifyAppHeadView'45'RVar'45'curry_2400 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'curry_2400 = erased
-- Once.TypeCheck.Soundness.infer-sound
d_infer'45'sound_2416 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'sound_2416 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'sound_2416 v0 v1
du_infer'45'sound_2416 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'sound_2416 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.check-sound
d_check'45'sound_2432 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_check'45'sound_2432 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'sound_2432 v0 v1 v2
du_check'45'sound_2432 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_check'45'sound_2432 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
