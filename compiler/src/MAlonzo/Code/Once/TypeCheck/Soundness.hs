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
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Soundness.sound-RInt
d_sound'45'RInt_20 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
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
-- Once.TypeCheck.Soundness.sound-RStringLit
d_sound'45'RStringLit_40 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RStringLit_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RStringLit_40
du_sound'45'RStringLit_40 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RStringLit_40
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
-- Once.TypeCheck.Soundness.sound-RUnit
d_sound'45'RUnit_58 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnit_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RUnit_58
du_sound'45'RUnit_58 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnit_58
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
-- Once.TypeCheck.Soundness.sound-RVar-unit
d_sound'45'RVar'45'unit_74 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RVar'45'unit_74
du_sound'45'RVar'45'unit_74 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit_74
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
-- Once.TypeCheck.Soundness.InferBundle
d_InferBundle_80 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_InferBundle_80 = erased
-- Once.TypeCheck.Soundness.inferBundle
d_inferBundle_92 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferBundle_92 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1292 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.CheckBundle
d_CheckBundle_100 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_CheckBundle_100 = erased
-- Once.TypeCheck.Soundness.checkBundle
d_checkBundle_116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkBundle_116 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1298 (coe v0)
         (coe v1) (coe v2))
      erased
-- Once.TypeCheck.Soundness.ViewBundle
d_ViewBundle_124 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_124 = erased
-- Once.TypeCheck.Soundness.viewBundle
d_viewBundle_132 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_132 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1008
         (coe v0))
      erased
-- Once.TypeCheck.Soundness.check-soundV
d_check'45'soundV_150 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_check'45'soundV_150 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'soundV_150 v0 v1 v2
du_check'45'soundV_150 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_check'45'soundV_150 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.infer-soundV
d_infer'45'soundV_238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'soundV_238 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'soundV_238 v0 v1
du_infer'45'soundV_238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'soundV_238 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.inferElab-eq-RInt
d_inferElab'45'eq'45'RInt_310 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RInt_310 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RStringLit
d_inferElab'45'eq'45'RStringLit_320 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RStringLit_320 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RUnit
d_inferElab'45'eq'45'RUnit_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RUnit_328 = erased
-- Once.TypeCheck.Soundness.sound-RUnaryOp-neg
d_sound'45'RUnaryOp'45'neg_358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnaryOp'45'neg_358 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RUnaryOp'45'neg_358 v0 v1
du_sound'45'RUnaryOp'45'neg_358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnaryOp'45'neg_358 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_1472
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RAnnot
d_sound'45'RAnnot_462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RAnnot_462 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sound'45'RAnnot_462 v0 v1 v2
du_sound'45'RAnnot_462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RAnnot_462 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_1466
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442 (coe v0)
                 (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RPair
d_sound'45'RPair_590 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RPair_590 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sound'45'RPair_590 v0 v1 v2
du_sound'45'RPair_590 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RPair_590 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RPair'45'aux_1458
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v1))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LookupBundle
d_LookupBundle_692 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LookupBundle_692 = erased
-- Once.TypeCheck.Soundness.lookupBundle
d_lookupBundle_704 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupBundle_704 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RQualified
d_sound'45'RQualified_726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RQualified_726 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RQualified_726 v0 v1 v2
du_sound'45'RQualified_726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RQualified_726 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_1524
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
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
d_LocalLookupBundle_808 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LocalLookupBundle_808 = erased
-- Once.TypeCheck.Soundness.localLookupBundle
d_localLookupBundle_820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_localLookupBundle_820 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_404 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.UnitDecBundle
d_UnitDecBundle_828 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_UnitDecBundle_828 = erased
-- Once.TypeCheck.Soundness.unitDecBundle
d_unitDecBundle_836 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unitDecBundle_836 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe ("unit" :: Data.Text.Text)))
      erased
-- Once.TypeCheck.Soundness.sound-RVar
d_sound'45'RVar_854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar_854 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RVar_854 v0 v1
du_sound'45'RVar_854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar_854 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                 (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("unit" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then let v5
                           = seq
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
                                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                           (coe v0)))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_328)
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> coe seq (coe v6) (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v5
                            = seq
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                                   (coe v0) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_404
                                      (coe v0) (coe v1))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                         (coe v0))
                                      (coe v1))) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> coe seq (coe v6) (coe v7)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-check-RVar-id
d_sound'45'check'45'RVar'45'id_934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_sound'45'check'45'RVar'45'id_934 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'check'45'RVar'45'id_934 v0 v1
du_sound'45'check'45'RVar'45'id_934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_sound'45'check'45'RVar'45'id_934 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'id'45'aux_1648
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                 (coe v0) (coe ("id" :: Data.Text.Text))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                    (coe ("id" :: Data.Text.Text))
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                    (coe ("id" :: Data.Text.Text)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RVar-unit-generic
d_sound'45'RVar'45'unit'45'generic_1010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit'45'generic_1010 v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'RVar'45'unit'45'generic_1010 v0
du_sound'45'RVar'45'unit'45'generic_1010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit'45'generic_1010 v0 v1
  = coe
      du_sound'45'RVar_854 (coe v0) (coe ("unit" :: Data.Text.Text))
-- Once.TypeCheck.Soundness.sound-RBinOp
d_sound'45'RBinOp_1056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RBinOp_1056 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11
  = du_sound'45'RBinOp_1056 v0 v1 v2 v3
du_sound'45'RBinOp_1056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RBinOp_1056 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_1482
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LetBodyBundle
d_LetBodyBundle_1172 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_LetBodyBundle_1172 = erased
-- Once.TypeCheck.Soundness.letBodyBundle
d_letBodyBundle_1192 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_letBodyBundle_1192 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1292
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.sound-RLet
d_sound'45'RLet_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RLet_1246 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'RLet_1246 v0 v1 v2 v3
du_sound'45'RLet_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RLet_1246 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_1492
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.CaseBranchBundle
d_CaseBranchBundle_1362 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_CaseBranchBundle_1362 = erased
-- Once.TypeCheck.Soundness.caseBranchBundle
d_caseBranchBundle_1382 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseBranchBundle_1382 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1292
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.TyEqBundle
d_TyEqBundle_1396 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_TyEqBundle_1396 = erased
-- Once.TypeCheck.Soundness.tyEqBundle
d_tyEqBundle_1408 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tyEqBundle_1408 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RDestruct
d_sound'45'RDestruct_1476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RDestruct_1476 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
                          ~v11 ~v12 ~v13 ~v14
  = du_sound'45'RDestruct_1476 v0 v1 v2 v3 v4 v5
du_sound'45'RDestruct_1476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RDestruct_1476 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v9 v10 v11 v12 v13
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v14 v15
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'43'__128 v14 v15
                         -> let v16
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                         (coe v0) (coe v2) (coe v14))
                                      (coe v3) in
                            coe
                              (case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                   -> case coe v17 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v19 v20 v21 v22 v23
                                          -> case coe v20 of
                                               MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v25 v26
                                                 -> let v27
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                                                 (coe v0) (coe v4) (coe v15))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v27 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                           -> case coe v28 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v30 v31 v32 v33 v34
                                                                  -> case coe v31 of
                                                                       MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v36 v37
                                                                         -> let v38
                                                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                                                      (coe v19)
                                                                                      (coe v30) in
                                                                            coe
                                                                              (case coe v38 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v39 v40
                                                                                   -> if coe v39
                                                                                        then let v41
                                                                                                   = seq
                                                                                                       (coe
                                                                                                          v40)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
                                                                                                             (coe
                                                                                                                v30)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                                                                                                (coe
                                                                                                                   v10)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'8852''7512'__114
                                                                                                                   (coe
                                                                                                                      v26)
                                                                                                                   (coe
                                                                                                                      v37)))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_case''_322
                                                                                                                v10
                                                                                                                v26
                                                                                                                v37
                                                                                                                v25
                                                                                                                v36
                                                                                                                v14
                                                                                                                v15
                                                                                                                v11
                                                                                                                v21
                                                                                                                v32)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                   (coe
                                                                                                                      v12)
                                                                                                                   (coe
                                                                                                                      addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v22)))
                                                                                                                (coe
                                                                                                                   addInt
                                                                                                                   (coe
                                                                                                                      (1 ::
                                                                                                                         Integer))
                                                                                                                   (coe
                                                                                                                      v33)))
                                                                                                             (coe
                                                                                                                v34))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166
                                                                                                             v14
                                                                                                             v15
                                                                                                             v25
                                                                                                             v36
                                                                                                             v10
                                                                                                             v26
                                                                                                             v37
                                                                                                             v8
                                                                                                             v18
                                                                                                             v29)) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v41 of
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                    -> coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v42)
                                                                                                         (coe
                                                                                                            v43)
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                        else (let v41
                                                                                                    = seq
                                                                                                        (coe
                                                                                                           v40)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_40))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                                              coe
                                                                                                (case coe
                                                                                                        v41 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                     -> coe
                                                                                                          seq
                                                                                                          (coe
                                                                                                             v42)
                                                                                                          (coe
                                                                                                             v43)
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v30
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v19
                                          -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v14
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Int_136
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Float_138
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Str_140
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Buffer_142
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v9
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LamBodyBundle
d_LamBodyBundle_1624 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_LamBodyBundle_1624 = erased
-- Once.TypeCheck.Soundness.lamBodyBundle
d_lamBodyBundle_1648 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lamBodyBundle_1648 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1298
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
            (coe v1) (coe v2))
         (coe v3) (coe v4))
      erased
-- Once.TypeCheck.Soundness.LeqBundle
d_LeqBundle_1664 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> ()
d_LeqBundle_1664 = erased
-- Once.TypeCheck.Soundness.leqBundle
d_leqBundle_1676 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leqBundle_1676 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1260 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-check-RLam
d_sound'45'check'45'RLam_1712 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_sound'45'check'45'RLam_1712 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9
                              ~v10 ~v11
  = du_sound'45'check'45'RLam_1712 v0 v1 v2 v3 v4 v5
du_sound'45'check'45'RLam_1712 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_sound'45'check'45'RLam_1712 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v9 v10 v11 v12
                  -> case coe v9 of
                       MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v14 v15
                         -> let v16
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1260
                                      (coe v14) (coe v4) in
                            coe
                              (case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> let v18
                                            = coe
                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320
                                                (coe v15)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_lam_208 v14
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12) in
                                      coe
                                        (let v19
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_568
                                                   v14 v8 in
                                         coe (coe seq (coe v18) (coe v19)))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_322 v9
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-id
d_sound'45'RApp'45'id_1852 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'id_1852 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'id_1852 v0 v1
du_sound'45'RApp'45'id_1852 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'id_1852 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__102
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_id_22) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-terminal
d_sound'45'RApp'45'terminal_1956 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'terminal_1956 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'terminal_1956 v0 v1
du_sound'45'RApp'45'terminal_1956 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'terminal_1956 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
                               (coe MAlonzo.Code.Once.Type.C_Unit_122)
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__102
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_terminal_74) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v5
                                  v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-fst
d_sound'45'RApp'45'fst_2060 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'fst_2060 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'fst_2060 v0 v1
du_sound'45'RApp'45'fst_2060 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'fst_2060 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> let v12
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 (coe v10)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__102
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                                         (coe MAlonzo.Code.Once.IR.C_fst_44) v7)
                                      (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                            coe
                              (let v13
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216
                                         v11 v6 v4 in
                               coe (coe seq (coe v12) (coe v13)))
                       MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Int_136
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Float_138
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Str_140
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Buffer_142
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-snd
d_sound'45'RApp'45'snd_2164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'snd_2164 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'snd_2164 v0 v1
du_sound'45'RApp'45'snd_2164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'snd_2164 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> let v12
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 (coe v11)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__102
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                                         (coe MAlonzo.Code.Once.IR.C_snd_50) v7)
                                      (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                            coe
                              (let v13
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228
                                         v10 v6 v4 in
                               coe (coe seq (coe v12) (coe v13)))
                       MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Int_136
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Float_138
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Str_140
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Buffer_142
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-arr
d_sound'45'RApp'45'arr_2268 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'arr_2268 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'arr_2268 v0 v1
du_sound'45'RApp'45'arr_2268 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'arr_2268 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_Zero_6
                                       -> let v15
                                                = seq
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_ArrNeedsFunction_34))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                          coe
                                            (case coe v15 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                 -> coe seq (coe v16) (coe v17)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     MAlonzo.Code.Once.Type.C_One_8
                                       -> let v15
                                                = seq
                                                    (coe v14)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_ArrNeedsFunction_34))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                          coe
                                            (case coe v15 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                 -> coe seq (coe v16) (coe v17)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     MAlonzo.Code.Once.Type.C_Many_10
                                       -> case coe v14 of
                                            MAlonzo.Code.Once.Type.C_pure_34
                                              -> let v15
                                                       = coe
                                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                              (coe v10)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe v13)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_eff_36))
                                                              (coe v12))
                                                           (coe v6)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                              v7)
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v8))
                                                           (coe v9) in
                                                 coe
                                                   (let v16
                                                          = coe
                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250
                                                              v4 in
                                                    coe (coe seq (coe v15) (coe v16)))
                                            MAlonzo.Code.Once.Type.C_eff_36
                                              -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Int_136
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Float_138
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Str_140
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Buffer_142
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-apply
d_sound'45'RApp'45'apply_2372 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'apply_2372 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'apply_2372 v0 v1
du_sound'45'RApp'45'apply_2372 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'apply_2372 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> case coe v10 of
                              MAlonzo.Code.Once.Type.C_Unit_122
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_Void_124
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_Zero_6
                                              -> let v17
                                                       = seq
                                                           (coe v16)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                    (coe
                                                                       ("apply"
                                                                        ::
                                                                        Data.Text.Text))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                 coe
                                                   (case coe v17 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                        -> coe seq (coe v18) (coe v19)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_One_8
                                              -> let v17
                                                       = seq
                                                           (coe v16)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                    (coe
                                                                       ("apply"
                                                                        ::
                                                                        Data.Text.Text))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                 coe
                                                   (case coe v17 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                        -> coe seq (coe v18) (coe v19)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> case coe v16 of
                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                     -> let v17
                                                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                                  (coe v12) (coe v11) in
                                                        coe
                                                          (case coe v17 of
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                               -> if coe v18
                                                                    then let v20
                                                                               = seq
                                                                                   (coe v19)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
                                                                                         (coe v14)
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__90
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                                                                  (coe
                                                                                                     v0)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__102
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  v6)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_app_224
                                                                                            (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                                                                  (coe
                                                                                                     v0)))
                                                                                            v6
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Type.C__'42'__126
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.d__'8658'__150
                                                                                                  (coe
                                                                                                     v12)
                                                                                                  (coe
                                                                                                     v14))
                                                                                               (coe
                                                                                                  v12))
                                                                                            v15
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1142
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                                                                  (coe
                                                                                                     v0))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Type.C__'42'__126
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Type.d__'8658'__150
                                                                                                        (coe
                                                                                                           v12)
                                                                                                        (coe
                                                                                                           v14))
                                                                                                     (coe
                                                                                                        v12))
                                                                                                  (coe
                                                                                                     v13)
                                                                                                  (coe
                                                                                                     v14))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Elaborate.d_specApply_496
                                                                                                  (coe
                                                                                                     v12)
                                                                                                  (coe
                                                                                                     v14)))
                                                                                            v7)
                                                                                         (coe
                                                                                            addInt
                                                                                            (coe
                                                                                               (1 ::
                                                                                                  Integer))
                                                                                            (coe
                                                                                               v8))
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262
                                                                                         v12 v6
                                                                                         v4)) in
                                                                         coe
                                                                           (case coe v20 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                -> coe
                                                                                     seq (coe v21)
                                                                                     (coe v22)
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    else (let v20
                                                                                = seq
                                                                                    (coe v19)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                             (coe
                                                                                                ("apply"
                                                                                                 ::
                                                                                                 Data.Text.Text))))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                          coe
                                                                            (case coe v20 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                 -> coe
                                                                                      seq (coe v21)
                                                                                      (coe v22)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Type.C_eff_36
                                                     -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_ν'45'type_134 v12
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_Int_136
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_Float_138
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_Str_140
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              MAlonzo.Code.Once.Type.C_Buffer_142
                                -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Int_136
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Float_138
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Str_140
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Buffer_142
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_298 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-generic
d_sound'45'RApp'45'generic_2490 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'generic_2490 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11
  = du_sound'45'RApp'45'generic_2490 v0 v1 v2
du_sound'45'RApp'45'generic_2490 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'generic_2490 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_1566
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1008
                 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-id
d_classifyAppHeadView'45'RVar'45'id_2588 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'id_2588 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-fst
d_classifyAppHeadView'45'RVar'45'fst_2590 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'fst_2590 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-snd
d_classifyAppHeadView'45'RVar'45'snd_2592 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'snd_2592 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-terminal
d_classifyAppHeadView'45'RVar'45'terminal_2594 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'terminal_2594 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-arr
d_classifyAppHeadView'45'RVar'45'arr_2596 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'arr_2596 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-apply
d_classifyAppHeadView'45'RVar'45'apply_2598 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'apply_2598 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inl
d_classifyAppHeadView'45'RVar'45'inl_2600 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inl_2600 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inr
d_classifyAppHeadView'45'RVar'45'inr_2602 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inr_2602 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-initial
d_classifyAppHeadView'45'RVar'45'initial_2604 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'initial_2604 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-curry
d_classifyAppHeadView'45'RVar'45'curry_2606 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'curry_2606 = erased
-- Once.TypeCheck.Soundness.infer-sound
d_infer'45'sound_2622 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'sound_2622 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'sound_2622 v0 v1
du_infer'45'sound_2622 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'sound_2622 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.check-sound
d_check'45'sound_2638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_check'45'sound_2638 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'sound_2638 v0 v1 v2
du_check'45'sound_2638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_check'45'sound_2638 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
