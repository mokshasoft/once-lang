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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Soundness.sound-RInt
d_sound'45'RInt_20 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
-- Once.TypeCheck.Soundness.sound-RStringLit
d_sound'45'RStringLit_40 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RStringLit_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RStringLit_40
du_sound'45'RStringLit_40 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RStringLit_40
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
-- Once.TypeCheck.Soundness.sound-RUnit
d_sound'45'RUnit_58 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnit_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RUnit_58
du_sound'45'RUnit_58 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnit_58
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
-- Once.TypeCheck.Soundness.sound-RVar-unit
d_sound'45'RVar'45'unit_74 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'RVar'45'unit_74
du_sound'45'RVar'45'unit_74 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit_74
  = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
-- Once.TypeCheck.Soundness.InferBundle
d_InferBundle_80 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_InferBundle_80 = erased
-- Once.TypeCheck.Soundness.inferBundle
d_inferBundle_92 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferBundle_92 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1716 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.CheckBundle
d_CheckBundle_100 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_CheckBundle_100 = erased
-- Once.TypeCheck.Soundness.checkBundle
d_checkBundle_116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkBundle_116 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1722 (coe v0)
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
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
         (coe v0))
      erased
-- Once.TypeCheck.Soundness.check-soundV
d_check'45'soundV_150 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_check'45'soundV_150 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'soundV_150 v0 v1 v2
du_check'45'soundV_150 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_check'45'soundV_150 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1890
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.infer-soundV
d_infer'45'soundV_238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'soundV_238 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'soundV_238 v0 v1
du_infer'45'soundV_238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'soundV_238 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.inferElab-eq-RInt
d_inferElab'45'eq'45'RInt_310 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RInt_310 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RStringLit
d_inferElab'45'eq'45'RStringLit_320 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RStringLit_320 = erased
-- Once.TypeCheck.Soundness.inferElab-eq-RUnit
d_inferElab'45'eq'45'RUnit_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'45'eq'45'RUnit_328 = erased
-- Once.TypeCheck.Soundness.sound-RUnaryOp-neg
d_sound'45'RUnaryOp'45'neg_358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RUnaryOp'45'neg_358 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RUnaryOp'45'neg_358 v0 v1
du_sound'45'RUnaryOp'45'neg_358 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RUnaryOp'45'neg_358 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'neg'45'aux_1932
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_366
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RAnnot
d_sound'45'RAnnot_462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RAnnot_462 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_sound'45'RAnnot_462 v0 v1 v2
du_sound'45'RAnnot_462 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RAnnot_462 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_1914
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1890
                 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RPair
d_sound'45'RPair_590 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RPair_590 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_sound'45'RPair_590 v0 v1 v2
du_sound'45'RPair_590 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RPair_590 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RPair'45'aux_1906
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
                 (coe v1))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
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
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RQualified
d_sound'45'RQualified_726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RQualified_726 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RQualified_726 v0 v1 v2
du_sound'45'RQualified_726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RQualified_726 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_2106
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_LocalLookupBundle_808 = erased
-- Once.TypeCheck.Soundness.localLookupBundle
d_localLookupBundle_820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_localLookupBundle_820 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572 (coe v0)
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar_854 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_sound'45'RVar_854 v0 v1
du_sound'45'RVar_854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
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
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316
                                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                           (coe v0)))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56)) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> coe seq (coe v6) (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v5
                            = seq
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2184
                                   (coe v0) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572
                                      (coe v0) (coe v1))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_sound'45'check'45'RVar'45'id_934 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_sound'45'check'45'RVar'45'id_934 v0 v1
du_sound'45'check'45'RVar'45'id_934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_sound'45'check'45'RVar'45'id_934 v0 v1
  = let v2 = "id" :: Data.Text.Text in
    coe
      (let v3
             = coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2184
                 (coe v0) (coe ("id" :: Data.Text.Text))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                    (coe ("id" :: Data.Text.Text))
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                    (coe ("id" :: Data.Text.Text))) in
       coe
         (case coe v3 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
              -> case coe v4 of
                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                     -> let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.du_embedOrSubsume_584
                                  (coe v1) (coe v3) in
                        coe
                          (case coe v11 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                               -> coe seq (coe v12) (coe v13)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v6
                     -> let v7
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                     (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        ("id" :: Data.Text.Text))) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                               -> if coe v8
                                    then let v10
                                               = seq
                                                   (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'id'45'aux_2302
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_2308
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_2314
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_2320
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_2326
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_2332
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286
                                                -> let v11
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_2338
                                                             (coe v0) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                          -> coe seq (coe v12) (coe v13)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290
                                                -> let v12
                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2346
                                                             (coe v0) (coe v2) (coe v1) (coe v3) in
                                                   coe
                                                     (case coe v12 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                          -> coe seq (coe v13) (coe v14)
                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    else (let v10
                                                = seq
                                                    (coe v9)
                                                    (let v10
                                                           = coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                               erased
                                                               (\ v10 ->
                                                                  coe
                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                    (coe v2))
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                  (coe v2)
                                                                  (coe
                                                                     ("fst" :: Data.Text.Text))) in
                                                     coe
                                                       (case coe v10 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                            -> if coe v11
                                                                 then coe
                                                                        seq (coe v12)
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276)
                                                                 else coe
                                                                        seq (coe v12)
                                                                        (let v13
                                                                               = coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                   erased
                                                                                   (\ v13 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                        (coe v2))
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                      (coe v2)
                                                                                      (coe
                                                                                         ("snd"
                                                                                          ::
                                                                                          Data.Text.Text))) in
                                                                         coe
                                                                           (case coe v13 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                -> if coe v14
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278)
                                                                                     else coe
                                                                                            seq
                                                                                            (coe
                                                                                               v15)
                                                                                            (let v16
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                       erased
                                                                                                       (\ v16 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                            (coe
                                                                                                               v2))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                          (coe
                                                                                                             v2)
                                                                                                          (coe
                                                                                                             ("terminal"
                                                                                                              ::
                                                                                                              Data.Text.Text))) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v16 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                    -> if coe
                                                                                                            v17
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v18)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280)
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v18)
                                                                                                                (let v19
                                                                                                                       = coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                           erased
                                                                                                                           (\ v19 ->
                                                                                                                              coe
                                                                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                (coe
                                                                                                                                   v2))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 ("initial"
                                                                                                                                  ::
                                                                                                                                  Data.Text.Text))) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v19 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                        -> if coe
                                                                                                                                v20
                                                                                                                             then coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v21)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282)
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v21)
                                                                                                                                    (let v22
                                                                                                                                           = coe
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                               erased
                                                                                                                                               (\ v22 ->
                                                                                                                                                  coe
                                                                                                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                    (coe
                                                                                                                                                       v2))
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                  (coe
                                                                                                                                                     v2)
                                                                                                                                                  (coe
                                                                                                                                                     ("inl"
                                                                                                                                                      ::
                                                                                                                                                      Data.Text.Text))) in
                                                                                                                                     coe
                                                                                                                                       (case coe
                                                                                                                                               v22 of
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                            -> if coe
                                                                                                                                                    v23
                                                                                                                                                 then coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v24)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v24)
                                                                                                                                                        (let v25
                                                                                                                                                               = coe
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                   erased
                                                                                                                                                                   (\ v25 ->
                                                                                                                                                                      coe
                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                        (coe
                                                                                                                                                                           v2))
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                      (coe
                                                                                                                                                                         v2)
                                                                                                                                                                      (coe
                                                                                                                                                                         ("inr"
                                                                                                                                                                          ::
                                                                                                                                                                          Data.Text.Text))) in
                                                                                                                                                         coe
                                                                                                                                                           (case coe
                                                                                                                                                                   v25 of
                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                                                -> if coe
                                                                                                                                                                        v26
                                                                                                                                                                     then coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v27)
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286)
                                                                                                                                                                     else coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v27)
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290)
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError)) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'id'45'aux_2302
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_2308
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_2314
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_2320
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_2326
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_2332
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286
                                                 -> let v11
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_2338
                                                              (coe v0) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe seq (coe v12) (coe v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290
                                                 -> let v12
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV'45'RVar'45'bbc'45'other'45'aux_2346
                                                              (coe v0) (coe v2) (coe v1) (coe v3) in
                                                    coe
                                                      (case coe v12 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                           -> coe seq (coe v13) (coe v14)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Soundness.sound-RVar-unit-generic
d_sound'45'RVar'45'unit'45'generic_1010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RVar'45'unit'45'generic_1010 v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_sound'45'RVar'45'unit'45'generic_1010 v0
du_sound'45'RVar'45'unit'45'generic_1010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RVar'45'unit'45'generic_1010 v0 v1
  = coe
      du_sound'45'RVar_854 (coe v0) (coe ("unit" :: Data.Text.Text))
-- Once.TypeCheck.Soundness.sound-RBinOp
d_sound'45'RBinOp_1056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RBinOp_1056 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_1980
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LetBodyBundle
d_LetBodyBundle_1172 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_LetBodyBundle_1172 = erased
-- Once.TypeCheck.Soundness.letBodyBundle
d_letBodyBundle_1192 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_letBodyBundle_1192 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1716
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
            (coe v1) (coe v2))
         (coe v3))
      erased
-- Once.TypeCheck.Soundness.sound-RLet
d_sound'45'RLet_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RLet_1246 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_sound'45'RLet_1246 v0 v1 v2 v3
du_sound'45'RLet_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RLet_1246 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_1990
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> coe seq (coe v5) (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.CaseBranchBundle
d_CaseBranchBundle_1362 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_CaseBranchBundle_1362 = erased
-- Once.TypeCheck.Soundness.caseBranchBundle
d_caseBranchBundle_1382 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseBranchBundle_1382 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1716
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
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
         MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-RDestruct
d_sound'45'RDestruct_1476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RDestruct_1476 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_2026
              (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> coe seq (coe v7) (coe v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.LamBodyBundle
d_LamBodyBundle_1624 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_LamBodyBundle_1624 = erased
-- Once.TypeCheck.Soundness.lamBodyBundle
d_lamBodyBundle_1648 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lamBodyBundle_1648 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1722
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
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
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1592 (coe v0)
         (coe v1))
      erased
-- Once.TypeCheck.Soundness.sound-check-RLam
d_sound'45'check'45'RLam_1712 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_sound'45'check'45'RLam_1712 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1890
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v9 v10 v11 v12
                  -> case coe v9 of
                       MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v15
                         -> let v16
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1592
                                      (coe v14) (coe v4) in
                            coe
                              (case coe v16 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> let v18
                                            = coe
                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340
                                                (coe v15)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v14
                                                   v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12) in
                                      coe
                                        (let v19
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_618
                                                   v14 v8 in
                                         coe (coe seq (coe v18) (coe v19)))
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_342 v9
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-id
d_sound'45'RApp'45'id_1852 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'id_1852 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'id_1852 v0 v1
du_sound'45'RApp'45'id_1852 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'id_1852 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__90
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__102
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_id_22) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_244 v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-terminal
d_sound'45'RApp'45'terminal_1956 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'terminal_1956 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'terminal_1956 v0 v1
du_sound'45'RApp'45'terminal_1956 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'terminal_1956 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316
                               (coe MAlonzo.Code.Once.Type.C_Unit_122)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__90
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__102
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                               (coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v6 v5
                                  (coe MAlonzo.Code.Once.IR.C_terminal_74) v7)
                               (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                     coe
                       (let v11
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_278 v5
                                  v6 v4 in
                        coe (coe seq (coe v10) (coe v11)))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-fst
d_sound'45'RApp'45'fst_2060 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'fst_2060 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'fst_2060 v0 v1
du_sound'45'RApp'45'fst_2060 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'fst_2060 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> let v12
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 (coe v10)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__90
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__102
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v6 v5
                                         (coe MAlonzo.Code.Once.IR.C_fst_44) v7)
                                      (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                            coe
                              (let v13
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_256
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-snd
d_sound'45'RApp'45'snd_2164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'snd_2164 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'snd_2164 v0 v1
du_sound'45'RApp'45'snd_2164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'snd_2164 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Unit_122
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C_Void_124
                         -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                       MAlonzo.Code.Once.Type.C__'42'__126 v10 v11
                         -> let v12
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 (coe v11)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__90
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__102
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6)))
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v6 v5
                                         (coe MAlonzo.Code.Once.IR.C_snd_50) v7)
                                      (coe addInt (coe (1 :: Integer)) (coe v8)) (coe v9) in
                            coe
                              (let v13
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_268
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-apply
d_sound'45'RApp'45'apply_2268 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'apply_2268 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_sound'45'RApp'45'apply_2268 v0 v1
du_sound'45'RApp'45'apply_2268 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'apply_2268 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
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
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                                                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
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
                                                                                         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316
                                                                                         (coe v14)
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__90
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                  (coe
                                                                                                     v0)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__102
                                                                                               (coe
                                                                                                  v15)
                                                                                               (coe
                                                                                                  v6)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378
                                                                                            v6
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Type.C__'42'__126
                                                                                               (coe
                                                                                                  v10)
                                                                                               (coe
                                                                                                  v12))
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.IR.C_apply_92)
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
                                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_290
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
                                                                                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.sound-RApp-generic
d_sound'45'RApp'45'generic_2386 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
   Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_sound'45'RApp'45'generic_2386 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                ~v9 ~v10 ~v11
  = du_sound'45'RApp'45'generic_2386 v0 v1 v2
du_sound'45'RApp'45'generic_2386 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_sound'45'RApp'45'generic_2386 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_2214
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
                 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-id
d_classifyAppHeadView'45'RVar'45'id_2484 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'id_2484 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-fst
d_classifyAppHeadView'45'RVar'45'fst_2486 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'fst_2486 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-snd
d_classifyAppHeadView'45'RVar'45'snd_2488 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'snd_2488 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-terminal
d_classifyAppHeadView'45'RVar'45'terminal_2490 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'terminal_2490 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-apply
d_classifyAppHeadView'45'RVar'45'apply_2492 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'apply_2492 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inl
d_classifyAppHeadView'45'RVar'45'inl_2494 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inl_2494 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-inr
d_classifyAppHeadView'45'RVar'45'inr_2496 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'inr_2496 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-initial
d_classifyAppHeadView'45'RVar'45'initial_2498 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'initial_2498 = erased
-- Once.TypeCheck.Soundness.classifyAppHeadView-RVar-curry
d_classifyAppHeadView'45'RVar'45'curry_2500 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHeadView'45'RVar'45'curry_2500 = erased
-- Once.TypeCheck.Soundness.infer-sound
d_infer'45'sound_2516 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_infer'45'sound_2516 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'sound_2516 v0 v1
du_infer'45'sound_2516 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_infer'45'sound_2516 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1874
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe seq (coe v3) (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Soundness.check-sound
d_check'45'sound_2532 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_check'45'sound_2532 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_check'45'sound_2532 v0 v1 v2
du_check'45'sound_2532 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_check'45'sound_2532 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1890
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe seq (coe v4) (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
