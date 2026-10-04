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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Soundness.sound-RInt
d_sound'45'RInt_20 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RInt_20 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RInt_20
du_sound'45'RInt_20 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RInt_20
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
-- Once.TypeCheck.Soundness.sound-RUnit
d_sound'45'RUnit_38 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnit_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RUnit_38
du_sound'45'RUnit_38 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnit_38
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
-- Once.TypeCheck.Soundness.sound-RVar-unit
d_sound'45'RVar'45'unit_54 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RVar'45'unit_54
du_sound'45'RVar'45'unit_54 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit_54
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
-- Once.TypeCheck.Soundness.InferBundle
d_InferBundle_60 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_InferBundle_60 = erased
-- Once.TypeCheck.Soundness.inferBundle
d_inferBundle_72 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferBundle_72 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9778 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.CheckBundle
d_CheckBundle_80 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_CheckBundle_80 = erased
-- Once.TypeCheck.Soundness.checkBundle
d_checkBundle_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkBundle_96 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_9792 (coe v0)
         (coe v1) (coe v2))
      erased
-- Once.TypeCheck.Soundness.ViewBundle
d_ViewBundle_104 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_104 = erased
-- Once.TypeCheck.Soundness.viewBundle
d_viewBundle_112 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_112 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
         (coe v0))
      erased
-- Once.TypeCheck.Soundness.check-soundV
d_check'45'soundV_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_check'45'soundV_130 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'soundV_130 v0 v1 v2
du_check'45'soundV_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_check'45'soundV_130 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.infer-soundV
d_infer'45'soundV_218 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'soundV_218 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'soundV_218 v0 v1
du_infer'45'soundV_218 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'soundV_218 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.inferElab-eq-RInt
d_inferElab'45'eq'45'RInt_290 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RInt_290 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RUnit
d_inferElab'45'eq'45'RUnit_298 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RUnit_298 = erased
-- Once.TypeCheck.Soundness.sound-RUnaryOp-neg
d_sound'45'RUnaryOp'45'neg_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnaryOp'45'neg_328 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RUnaryOp'45'neg_328 v0 v1
du_sound'45'RUnaryOp'45'neg_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnaryOp'45'neg_328 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'neg'45'aux_6200
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RAnnot_432 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sound'45'RAnnot_432 v0 v1 v2
du_sound'45'RAnnot_432 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RAnnot_432 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2718
              (coe v2)
              (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172 (coe v0)
                 (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RPair
d_sound'45'RPair_560 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RPair_560 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sound'45'RPair_560 v0 v1 v2
du_sound'45'RPair_560 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RPair_560 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RPair'45'aux_2664
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v1))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
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
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RQualified
d_sound'45'RQualified_696 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RQualified_696 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RQualified_696 v0 v1 v2
du_sound'45'RQualified_696 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RQualified_696 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_4390
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                 (coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("." :: Data.Text.Text) v1))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LocalLookupBundle
d_LocalLookupBundle_778 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LocalLookupBundle_778 = erased
-- Once.TypeCheck.Soundness.localLookupBundle
d_localLookupBundle_790 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_localLookupBundle_790 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_584 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.UnitDecBundle
d_UnitDecBundle_798 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_UnitDecBundle_798 = erased
-- Once.TypeCheck.Soundness.unitDecBundle
d_unitDecBundle_806 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unitDecBundle_806 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe ("unit" :: Data.Text.Text)))
      erased
-- Once.TypeCheck.Soundness.sound-RVar
d_sound'45'RVar_824 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar_824 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RVar_824 v0 v1
du_sound'45'RVar_824 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar_824 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_4702
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_496
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0))
                 (coe v1)
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_394 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-check-RVar-id
d_sound'45'check'45'RVar'45'id_904 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_sound'45'check'45'RVar'45'id_904 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'check'45'RVar'45'id_904 v0 v1
du_sound'45'check'45'RVar'45'id_904 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_sound'45'check'45'RVar'45'id_904 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_4740
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
d_sound'45'RVar'45'unit'45'generic_980 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit'45'generic_980 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'RVar'45'unit'45'generic_980
du_sound'45'RVar'45'unit'45'generic_980 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit'45'generic_980 v0
  = coe du_sound'45'RVar'45'unit_54
-- Once.TypeCheck.Soundness.sound-RBinOp
d_sound'45'RBinOp_1026 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RBinOp_1026 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11
  = du_sound'45'RBinOp_1026 v0 v1 v2 v3
du_sound'45'RBinOp_1026 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RBinOp_1026 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_2936
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LetBodyBundle
d_LetBodyBundle_1142 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_LetBodyBundle_1142 = erased
-- Once.TypeCheck.Soundness.letBodyBundle
d_letBodyBundle_1162 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_letBodyBundle_1162 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9778
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.sound-RLet
d_sound'45'RLet_1216 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RLet_1216 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'RLet_1216 v0 v1 v2 v3
du_sound'45'RLet_1216 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RLet_1216 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6218
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.CaseBranchBundle
d_CaseBranchBundle_1332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_CaseBranchBundle_1332 = erased
-- Once.TypeCheck.Soundness.caseBranchBundle
d_caseBranchBundle_1352 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseBranchBundle_1352 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_9778
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.TyEqBundle
d_TyEqBundle_1366 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_TyEqBundle_1366 = erased
-- Once.TypeCheck.Soundness.tyEqBundle
d_tyEqBundle_1378 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tyEqBundle_1378 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v0) (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RDestruct
d_sound'45'RDestruct_1446 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RDestruct_1446 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 ~v13 ~v14
  = du_sound'45'RDestruct_1446 v0 v1 v2 v3 v4 v5
du_sound'45'RDestruct_1446 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RDestruct_1446 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6232
              (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe seq (coe v7) (coe v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LamBodyBundle
d_LamBodyBundle_1594 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_LamBodyBundle_1594 = erased
-- Once.TypeCheck.Soundness.lamBodyBundle
d_lamBodyBundle_1618 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lamBodyBundle_1618 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_9792
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
            (coe v1) (coe v2))
         (coe v3) (coe v4))
      erased
-- Once.TypeCheck.Soundness.LeqBundle
d_LeqBundle_1634 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> ()
d_LeqBundle_1634 = erased
-- Once.TypeCheck.Soundness.leqBundle
d_leqBundle_1646 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leqBundle_1646 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1252 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-check-RLam
d_sound'45'check'45'RLam_1682 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_sound'45'check'45'RLam_1682 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
                              ~v10 ~v11
  = du_sound'45'check'45'RLam_1682 v0 v1 v2 v3 v4 v5
du_sound'45'check'45'RLam_1682 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_sound'45'check'45'RLam_1682 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v9 v10 v11 v12
                  -> case coe v9 of
                       MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v15
                         -> let v16
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1252
                                      (coe v14) (coe v4) in
                            coe
                              (case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> let v18
                                            = coe
                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112
                                                (coe v15)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v14
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12) in
                                      coe
                                        (let v19
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638
                                                   v14 v8 in
                                         coe (coe seq (coe v18) (coe v19)))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v9
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-id
d_sound'45'RApp'45'id_1822 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'id_1822 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'id_1822 v0 v1
du_sound'45'RApp'45'id_1822 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'id_1822 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
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
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_id_20) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-terminal
d_sound'45'RApp'45'terminal_1926 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'terminal_1926 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'terminal_1926 v0 v1
du_sound'45'RApp'45'terminal_1926 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'terminal_1926 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88
                               (coe MAlonzo.Code.Once.Type.C_Unit_120)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_terminal_72) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v5
                                  v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-fst
d_sound'45'RApp'45'fst_2030 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'fst_2030 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'fst_2030 v0 v1
du_sound'45'RApp'45'fst_2030 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'fst_2030 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2372 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-snd
d_sound'45'RApp'45'snd_2134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'snd_2134 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'snd_2134 v0 v1
du_sound'45'RApp'45'snd_2134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'snd_2134 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2448 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-apply
d_sound'45'RApp'45'apply_2238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'apply_2238 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'apply_2238 v0 v1
du_sound'45'RApp'45'apply_2238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'apply_2238 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2634 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-generic
d_sound'45'RApp'45'generic_2356 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'generic_2356 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11
  = du_sound'45'RApp'45'generic_2356 v0 v1 v2
du_sound'45'RApp'45'generic_2356 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'generic_2356 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6280
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-id
d_classifyAppHeadView'45'RVar'45'id_2454 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'id_2454 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-fst
d_classifyAppHeadView'45'RVar'45'fst_2456 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'fst_2456 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-snd
d_classifyAppHeadView'45'RVar'45'snd_2458 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'snd_2458 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-terminal
d_classifyAppHeadView'45'RVar'45'terminal_2460 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'terminal_2460 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-apply
d_classifyAppHeadView'45'RVar'45'apply_2462 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'apply_2462 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inl
d_classifyAppHeadView'45'RVar'45'inl_2464 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inl_2464 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inr
d_classifyAppHeadView'45'RVar'45'inr_2466 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inr_2466 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-initial
d_classifyAppHeadView'45'RVar'45'initial_2468 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'initial_2468 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-curry
d_classifyAppHeadView'45'RVar'45'curry_2470 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'curry_2470 = erased
-- Once.TypeCheck.Soundness.infer-sound
d_infer'45'sound_2486 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'sound_2486 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'sound_2486 v0 v1
du_infer'45'sound_2486 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'sound_2486 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.check-sound
d_check'45'sound_2502 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_check'45'sound_2502 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'sound_2502 v0 v1 v2
du_check'45'sound_2502 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_check'45'sound_2502 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
