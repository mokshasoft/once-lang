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

module MAlonzo.Code.Once.TypeCheck.ElaborateProofs where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Float.Representable
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RInt
d_checkElab'45'fallback'45'RInt_16 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RFloat
d_checkElab'45'fallback'45'RFloat_54 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Once.Float.Representable.T_Accepted_94 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_54 v0 ~v1 ~v2 ~v3 v4 v5
  = du_checkElab'45'fallback'45'RFloat_54 v0 v4 v5
du_checkElab'45'fallback'45'RFloat_54 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Once.Float.Representable.T_Accepted_94 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_54 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_float_198 v1
         (MAlonzo.Code.Once.Float.Representable.d_fits'45'all_110 (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RStringLit
d_checkElab'45'fallback'45'RStringLit_106 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RStringLit_106 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_134 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RQualified
d_checkElab'45'fallback'45'RQualified_170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_170 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8
  = du_checkElab'45'fallback'45'RQualified_170 v0 v1 v2
du_checkElab'45'fallback'45'RQualified_170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_170 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_2010
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
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v6) (coe v6) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v10) erased)))
                                 else coe
                                        seq (coe v13)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RResolved
d_checkElab'45'fallback'45'RResolved_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RResolved_328 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7
  = du_checkElab'45'fallback'45'RResolved_328 v0 v1
du_checkElab'45'fallback'45'RResolved_328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_328 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RResolved'45'aux_2018
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe
                    MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> let v10
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v5) (coe v5) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) erased)))
                                 else coe
                                        seq (coe v12)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RAnnot
d_checkElab'45'fallback'45'RAnnot_472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_472 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RAnnot_472 v0 v1 v2
du_checkElab'45'fallback'45'RAnnot_472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_472 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_1868
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1844
                 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v2) (coe v2) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v10) erased)))
                                 else coe
                                        seq (coe v13)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RLet
d_checkElab'45'fallback'45'RLet_620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_620 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkElab'45'fallback'45'RLet_620 v0 v1 v2 v3
du_checkElab'45'fallback'45'RLet_620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_620 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_1894
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v7) (coe v7) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then coe
                                        seq (coe v14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11) erased)))
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RDestruct
d_checkElab'45'fallback'45'RDestruct_800 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_800 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                         ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RDestruct_800 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RDestruct_800 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_800 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_1930
              (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v9 v10 v11 v12 v13
                  -> let v14
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v9) (coe v9) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                            -> if coe v15
                                 then coe
                                        seq (coe v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v13) erased)))
                                 else coe
                                        seq (coe v16)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnaryOp
d_checkElab'45'fallback'45'RUnaryOp_1002 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_1002 v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_1002 v0 v2
du_checkElab'45'fallback'45'RUnaryOp_1002 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_1002 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v5 v6 v7 v8 v9
                  -> let v10
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v5) (coe v5) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) erased)))
                                 else coe
                                        seq (coe v12)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_1148 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_1148 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-lookup-aux-fail
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_1172 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_1172 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-bridge
d_inferElabV'45'RVar'45'poly'45'bridge_1184 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'bridge_1184 = erased
-- Once.TypeCheck.ElaborateProofs._.helper
d_helper_1234 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_1234 = erased
-- Once.TypeCheck.ElaborateProofs._.bridge-eq
d_bridge'45'eq_1236 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'eq_1236 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-eq
d_inferElabV'45'RVar'45'poly'45'aux'45'eq_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_BareBuiltinClass_1272 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'eq_1246 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_1260 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_1260 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_1276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_1276 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_1288 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_1288
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_1306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_1306
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_1330 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_1330 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-fail-bridge
d_inferElabV'45'RVar'45'fail'45'bridge_1356 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'fail'45'bridge_1356 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_1380 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_1380 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'id_1380 v0 v1
du_checkElab'45'fallback'45'RVar'45'id_1380 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_1380 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
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
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                seq (coe v3)
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("id" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> coe
                                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("id" :: Data.Text.Text)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v7
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v1) (coe v1) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                            -> if coe v8
                                                 then coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                                              (coe MAlonzo.Code.Once.IR.C_id_22))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0))
                                                                 erased)))
                                                 else coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs._.just≢nothing
d_just'8802'nothing_1454 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_184 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_LookupImportView_632 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1454 = erased
-- Once.TypeCheck.ElaborateProofs._.just≢nothing
d_just'8802'nothing_1474 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_LookupLocalView_582 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1474 = erased
-- Once.TypeCheck.ElaborateProofs.just≢nothing-Maybe
d_just'8802'nothing'45'Maybe_1480 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_1480 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_1494 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_1494 v0 v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'fst_1494 v0 v1
du_checkElab'45'fallback'45'RVar'45'fst_1494 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_1494 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("fst" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("fst" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("fst" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                seq (coe v3)
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("fst" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> coe
                                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("fst" :: Data.Text.Text)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v7
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v1) (coe v1) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                            -> if coe v8
                                                 then coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                                              (coe MAlonzo.Code.Once.IR.C_fst_44))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0))
                                                                 erased)))
                                                 else coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_1596 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_1596 v0 ~v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'snd_1596 v0 v2
du_checkElab'45'fallback'45'RVar'45'snd_1596 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_1596 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("snd" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("snd" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("snd" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                seq (coe v3)
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("snd" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> coe
                                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("snd" :: Data.Text.Text)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v7
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v1) (coe v1) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                            -> if coe v8
                                                 then coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                                              (coe MAlonzo.Code.Once.IR.C_snd_50))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0))
                                                                 erased)))
                                                 else coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_1698 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_1698 v0 ~v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'terminal_1698 v0
du_checkElab'45'fallback'45'RVar'45'terminal_1698 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_1698 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("terminal" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("terminal" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("terminal" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> coe
                seq (coe v2)
                (let v4
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("terminal" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> coe
                                    seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("terminal" :: Data.Text.Text)) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                          (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe (0 :: Integer))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                (coe v0))
                                             erased))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminalV
d_checkElab'45'fallback'45'RVar'45'terminalV_1766 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_1766 v0 ~v1 ~v2 ~v3
                                                  ~v4
  = du_checkElab'45'fallback'45'RVar'45'terminalV_1766 v0
du_checkElab'45'fallback'45'RVar'45'terminalV_1766 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_1766 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("terminal" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("terminal" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("terminal" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> coe
                seq (coe v2)
                (let v4
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("terminal" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> coe
                                    seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("terminal" :: Data.Text.Text)) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                          (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe (0 :: Integer))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_560
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_412))
                                                erased)))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_1830 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_1830 v0 ~v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'initial_1830 v0
du_checkElab'45'fallback'45'RVar'45'initial_1830 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_1830 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("initial" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("initial" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("initial" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> coe
                seq (coe v2)
                (let v4
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("initial" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                               -> coe
                                    seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v5
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("initial" :: Data.Text.Text)) in
                           coe
                             (case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                          (coe MAlonzo.Code.Once.IR.C_initial_78))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe (0 :: Integer))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                (coe v0))
                                             erased))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_1896 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_1896 v0 v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inl_1896 v0 v1
du_checkElab'45'fallback'45'RVar'45'inl_1896 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_1896 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("inl" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("inl" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("inl" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                seq (coe v3)
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("inl" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> coe
                                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("inl" :: Data.Text.Text)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v7
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v1) (coe v1) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                            -> if coe v8
                                                 then coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_inl_56
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0))
                                                                 erased)))
                                                 else coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_1998 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_1998 v0 ~v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inr_1998 v0 v2
du_checkElab'45'fallback'45'RVar'45'inr_1998 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_1998 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
              (coe v0) (coe ("inr" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                 (coe ("inr" :: Data.Text.Text))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe ("inr" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> coe
                seq (coe v3)
                (let v5
                       = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                           (coe ("inr" :: Data.Text.Text))
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v6 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                               -> coe
                                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                        -> let v6
                                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                                     (coe ("inr" :: Data.Text.Text)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v7
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v1) (coe v1) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                            -> if coe v8
                                                 then coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_inr_62
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0))
                                                                 erased)))
                                                 else coe
                                                        seq (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkInGo-J
d_checkInGo'45'J_2098 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2098 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_2130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_2130 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkInGo'45'just'45'success_2130 v0 v1 v2 v3
du_checkInGo'45'just'45'success_2130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_2130 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1844
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2)
                 (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v7 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7
                          (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                             (coe v2) (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v2)))
                          (coe
                             MAlonzo.Code.Once.IR.C_In_96
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v2) (coe v3))
                             (coe MAlonzo.Code.Once.IR.C_Heap_8))
                          v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v9))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-In
d_checkElab'45'fallback'45'RApp'45'In_2182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_2182 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'In_2182 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'In_2182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_2182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_2130 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_2130 (coe v0) (coe v1) (coe v2)
                  (coe v3))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_checkInGo'45'just'45'success_2130 (coe v0) (coe v1) (coe v2)
                        (coe v3)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_2220 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_2220 v0 v1 v2 v3 ~v4 ~v5
                                              ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply_2220 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply_2220 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_2220 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                       -> coe
                                            seq (coe v17)
                                            (coe
                                               seq (coe v18)
                                               (let v19
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v19 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                       -> if coe v20
                                                            then coe
                                                                   seq (coe v21)
                                                                   (let v22
                                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                              (coe v3) (coe v3) in
                                                                    coe
                                                                      (case coe v22 of
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                           -> if coe v23
                                                                                then coe
                                                                                       seq (coe v24)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378
                                                                                             v8
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Type.C__'42'__126
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                   (coe
                                                                                                      v2)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Type.C_pure_34))
                                                                                                   (coe
                                                                                                      v3))
                                                                                                (coe
                                                                                                   v2))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.IR.C_apply_92)
                                                                                             v9)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v10))
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                (coe
                                                                                                   v11)
                                                                                                erased)))
                                                                                else coe
                                                                                       seq (coe v24)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                            else coe
                                                                   seq (coe v21)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.resolveExprWF
d_resolveExprWF_2308 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExprWF_2308 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_resolveExprWF_2308 v0 v1 v3 v4 v6 v7 v8 v9
du_resolveExprWF_2308 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExprWF_2308 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_16 v10
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v11 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v11
                    (coe
                       du_resolveExprWF_2308 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v17))
                       (coe v19) (coe v3) (coe v4) (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_48 v10 v11 v12 v14
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v14)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v15))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v10 v11 v12 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v10 v11 v12
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v18))
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__126 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1) (coe v16) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v14))
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1) (coe v17) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v12
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v12))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v11 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v11) (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__128 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_112
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__128 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_124
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1) (coe v15) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v10 v11 v12 v13 v14 v15 v16 v18 v19 v20
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v10 v11 v12 v13 v14
             v15 v16
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v15) (coe v16))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v18))
             (coe
                du_resolveExprWF_2308 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v19))
             (coe
                du_resolveExprWF_2308 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v16))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v20))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_162
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v10 v11 v12 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v10 v11 v12 v13
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v15))
             (coe
                du_resolveExprWF_2308 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v13))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v10
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v10
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v10 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_198 v10 v11
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_208 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_div_238 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_238 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_248 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_248 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_256 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_256
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_266 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_266 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_le_276 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_276 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_286 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_286 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_296 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_296 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_306 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_306 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_316 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_316 v10 v11
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_328 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                    (coe
                       du_resolveExprWF_2308 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v14) (coe v16))
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_336 v11 v12
        -> let v13
                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                     (coe v5)
                     (coe
                        MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v11)) in
           coe
             (case coe v13 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                  -> coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closure_344
                       (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v11))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_336 v11 v12
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_344 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_344 v11
      MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v10
        -> coe
             du_resolvePolyCase_2322 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v10) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48 (coe v3)
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366 v13
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_366 v13
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v10 v11 v13
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1) (coe v11) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_390 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_390 v13
                                  (coe
                                     du_resolveExprWF_2308 (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v18)
                                           (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                        (coe v17))
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_402 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v20
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_402 v13
                                  (coe
                                     du_resolveExprWF_2308 (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v20)
                                           (coe v15)))
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolvePolyCase
d_resolvePolyCase_2322 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvePolyCase_2322 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_resolvePolyCase_2322 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_resolvePolyCase_2322 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvePolyCase_2322 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    du_applySplice_2338 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1676
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v6)
                             (coe v2)))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.applySplice
d_applySplice_2338 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_applySplice_2338 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12
  = du_applySplice_2338 v0 v1 v2 v4 v5 v6 v7 v8 v12
du_applySplice_2338 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_applySplice_2338 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v9 v10 v11 v12
        -> coe
             seq (coe v9)
             (coe
                du_resolveExprWF_2308 (coe v0) (coe v1) (coe v7)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v6)
                   (coe v2))
                (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1154 (coe v1)
                   (coe v7) (coe v10)))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_342 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_2878 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExpr_2878 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_resolveExpr_2878 v0 v1 v3 v4 v5 v6 v7 v8
du_resolveExpr_2878 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExpr_2878 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_resolveExprWF_2308 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_2904 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_2904 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_2932 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_2932 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_2960 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_2960 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_2986 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_2986 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_3012 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_3012 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_3034 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_3034 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_3056 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_3056 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_3078 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_3078 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_3100 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_3100 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_3136 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_3136 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_3150 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_3150 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_3170 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_3170 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_3198 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_3198 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_3214 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_3214 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-str
d_resolveExpr'45'str_3230 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'str_3230 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_3252 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'add_3252 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_3274 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sub_3274 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_3296 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mul_3296 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_3318 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'div_3318 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_3340 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mod''_3340 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_3358 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_3358 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_3380 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lt_3380 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_3402 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'le_3402 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_3424 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'gt_3424 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_3446 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ge_3446 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_3468 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'eq_3468 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_3490 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ne_3490 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-arr'
d_resolveExpr'45'arr''_3512 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'arr''_3512 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_3532 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp'45'extern_3532 = erased
-- Once.TypeCheck.ElaborateProofs.acc-step-at-poly
d_acc'45'step'45'at'45'poly_3548 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_acc'45'step'45'at'45'poly_3548 = erased
-- Once.TypeCheck.ElaborateProofs.applySplice-eq-irrel
d_applySplice'45'eq'45'irrel_3586 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applySplice'45'eq'45'irrel_3586 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-poly-match
d_resolveExpr'45'poly'45'match_3654 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'poly'45'match_3654 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_3702 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_3702 v0 v1 ~v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RVar'45'poly_3702 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly_3702 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_3702 v0 v1
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
                            -> coe
                                 seq (coe v6)
                                 (let v8
                                        = let v8
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v8 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                       (coe
                                                          MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                          v1)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                          ("id" :: Data.Text.Text))) in
                                          coe
                                            (case coe v8 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                 -> if coe v9
                                                      then coe
                                                             seq (coe v10)
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274)
                                                      else coe
                                                             seq (coe v10)
                                                             (let v11
                                                                    = coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                        erased
                                                                        (\ v11 ->
                                                                           coe
                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                             (coe v1))
                                                                        (coe
                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                           (coe v1)
                                                                           (coe
                                                                              ("fst"
                                                                               ::
                                                                               Data.Text.Text))) in
                                                              coe
                                                                (case coe v11 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                     -> if coe v12
                                                                          then coe
                                                                                 seq (coe v13)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276)
                                                                          else coe
                                                                                 seq (coe v13)
                                                                                 (let v14
                                                                                        = coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                            erased
                                                                                            (\ v14 ->
                                                                                               coe
                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                 (coe
                                                                                                    v1))
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                               (coe
                                                                                                  v1)
                                                                                               (coe
                                                                                                  ("snd"
                                                                                                   ::
                                                                                                   Data.Text.Text))) in
                                                                                  coe
                                                                                    (case coe v14 of
                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                         -> if coe
                                                                                                 v15
                                                                                              then coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278)
                                                                                              else coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v16)
                                                                                                     (let v17
                                                                                                            = coe
                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                erased
                                                                                                                (\ v17 ->
                                                                                                                   coe
                                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                     (coe
                                                                                                                        v1))
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                   (coe
                                                                                                                      v1)
                                                                                                                   (coe
                                                                                                                      ("terminal"
                                                                                                                       ::
                                                                                                                       Data.Text.Text))) in
                                                                                                      coe
                                                                                                        (case coe
                                                                                                                v17 of
                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                             -> if coe
                                                                                                                     v18
                                                                                                                  then coe
                                                                                                                         seq
                                                                                                                         (coe
                                                                                                                            v19)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280)
                                                                                                                  else coe
                                                                                                                         seq
                                                                                                                         (coe
                                                                                                                            v19)
                                                                                                                         (let v20
                                                                                                                                = coe
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                    erased
                                                                                                                                    (\ v20 ->
                                                                                                                                       coe
                                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                         (coe
                                                                                                                                            v1))
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                       (coe
                                                                                                                                          v1)
                                                                                                                                       (coe
                                                                                                                                          ("initial"
                                                                                                                                           ::
                                                                                                                                           Data.Text.Text))) in
                                                                                                                          coe
                                                                                                                            (case coe
                                                                                                                                    v20 of
                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                 -> if coe
                                                                                                                                         v21
                                                                                                                                      then coe
                                                                                                                                             seq
                                                                                                                                             (coe
                                                                                                                                                v22)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282)
                                                                                                                                      else coe
                                                                                                                                             seq
                                                                                                                                             (coe
                                                                                                                                                v22)
                                                                                                                                             (let v23
                                                                                                                                                    = coe
                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                        erased
                                                                                                                                                        (\ v23 ->
                                                                                                                                                           coe
                                                                                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                             (coe
                                                                                                                                                                v1))
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                           (coe
                                                                                                                                                              v1)
                                                                                                                                                           (coe
                                                                                                                                                              ("inl"
                                                                                                                                                               ::
                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                              coe
                                                                                                                                                (case coe
                                                                                                                                                        v23 of
                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                     -> if coe
                                                                                                                                                             v24
                                                                                                                                                          then coe
                                                                                                                                                                 seq
                                                                                                                                                                 (coe
                                                                                                                                                                    v25)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284)
                                                                                                                                                          else coe
                                                                                                                                                                 seq
                                                                                                                                                                 (coe
                                                                                                                                                                    v25)
                                                                                                                                                                 (let v26
                                                                                                                                                                        = coe
                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                            erased
                                                                                                                                                                            (\ v26 ->
                                                                                                                                                                               coe
                                                                                                                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v1))
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                               (coe
                                                                                                                                                                                  v1)
                                                                                                                                                                               (coe
                                                                                                                                                                                  ("inr"
                                                                                                                                                                                   ::
                                                                                                                                                                                   Data.Text.Text))) in
                                                                                                                                                                  coe
                                                                                                                                                                    (case coe
                                                                                                                                                                            v26 of
                                                                                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                         -> if coe
                                                                                                                                                                                 v27
                                                                                                                                                                              then coe
                                                                                                                                                                                     seq
                                                                                                                                                                                     (coe
                                                                                                                                                                                        v28)
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286)
                                                                                                                                                                              else coe
                                                                                                                                                                                     seq
                                                                                                                                                                                     (coe
                                                                                                                                                                                        v28)
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290)
                                                                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError) in
                                  coe
                                    (coe
                                       seq (coe v8)
                                       (let v9
                                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                     (coe v0))
                                                  (coe v1) in
                                        coe
                                          (coe
                                             seq (coe v9)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v1)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe (0 :: Integer))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                         (coe v0))
                                                      erased)))))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v5
                            = seq
                                (coe v4)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
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
                             -> coe
                                  seq (coe v6)
                                  (let v8
                                         = let v8
                                                 = coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                     erased
                                                     (\ v8 ->
                                                        coe
                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                          (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                        (coe
                                                           MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           v1)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                           ("id" :: Data.Text.Text))) in
                                           coe
                                             (case coe v8 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                  -> if coe v9
                                                       then coe
                                                              seq (coe v10)
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274)
                                                       else coe
                                                              seq (coe v10)
                                                              (let v11
                                                                     = coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                         erased
                                                                         (\ v11 ->
                                                                            coe
                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                              (coe v1))
                                                                         (coe
                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                            (coe v1)
                                                                            (coe
                                                                               ("fst"
                                                                                ::
                                                                                Data.Text.Text))) in
                                                               coe
                                                                 (case coe v11 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                      -> if coe v12
                                                                           then coe
                                                                                  seq (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276)
                                                                           else coe
                                                                                  seq (coe v13)
                                                                                  (let v14
                                                                                         = coe
                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                             erased
                                                                                             (\ v14 ->
                                                                                                coe
                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                  (coe
                                                                                                     v1))
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                (coe
                                                                                                   v1)
                                                                                                (coe
                                                                                                   ("snd"
                                                                                                    ::
                                                                                                    Data.Text.Text))) in
                                                                                   coe
                                                                                     (case coe
                                                                                             v14 of
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                          -> if coe
                                                                                                  v15
                                                                                               then coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v16)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278)
                                                                                               else coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v16)
                                                                                                      (let v17
                                                                                                             = coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                 erased
                                                                                                                 (\ v17 ->
                                                                                                                    coe
                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                      (coe
                                                                                                                         v1))
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                    (coe
                                                                                                                       v1)
                                                                                                                    (coe
                                                                                                                       ("terminal"
                                                                                                                        ::
                                                                                                                        Data.Text.Text))) in
                                                                                                       coe
                                                                                                         (case coe
                                                                                                                 v17 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                              -> if coe
                                                                                                                      v18
                                                                                                                   then coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v19)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280)
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v19)
                                                                                                                          (let v20
                                                                                                                                 = coe
                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                     erased
                                                                                                                                     (\ v20 ->
                                                                                                                                        coe
                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                          (coe
                                                                                                                                             v1))
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                        (coe
                                                                                                                                           v1)
                                                                                                                                        (coe
                                                                                                                                           ("initial"
                                                                                                                                            ::
                                                                                                                                            Data.Text.Text))) in
                                                                                                                           coe
                                                                                                                             (case coe
                                                                                                                                     v20 of
                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                  -> if coe
                                                                                                                                          v21
                                                                                                                                       then coe
                                                                                                                                              seq
                                                                                                                                              (coe
                                                                                                                                                 v22)
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282)
                                                                                                                                       else coe
                                                                                                                                              seq
                                                                                                                                              (coe
                                                                                                                                                 v22)
                                                                                                                                              (let v23
                                                                                                                                                     = coe
                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                         erased
                                                                                                                                                         (\ v23 ->
                                                                                                                                                            coe
                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                              (coe
                                                                                                                                                                 v1))
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                            (coe
                                                                                                                                                               v1)
                                                                                                                                                            (coe
                                                                                                                                                               ("inl"
                                                                                                                                                                ::
                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                               coe
                                                                                                                                                 (case coe
                                                                                                                                                         v23 of
                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                      -> if coe
                                                                                                                                                              v24
                                                                                                                                                           then coe
                                                                                                                                                                  seq
                                                                                                                                                                  (coe
                                                                                                                                                                     v25)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284)
                                                                                                                                                           else coe
                                                                                                                                                                  seq
                                                                                                                                                                  (coe
                                                                                                                                                                     v25)
                                                                                                                                                                  (let v26
                                                                                                                                                                         = coe
                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                             erased
                                                                                                                                                                             (\ v26 ->
                                                                                                                                                                                coe
                                                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v1))
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                (coe
                                                                                                                                                                                   v1)
                                                                                                                                                                                (coe
                                                                                                                                                                                   ("inr"
                                                                                                                                                                                    ::
                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                   coe
                                                                                                                                                                     (case coe
                                                                                                                                                                             v26 of
                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                          -> if coe
                                                                                                                                                                                  v27
                                                                                                                                                                               then coe
                                                                                                                                                                                      seq
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v28)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286)
                                                                                                                                                                               else coe
                                                                                                                                                                                      seq
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v28)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290)
                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                _ -> MAlonzo.RTE.mazUnreachableError) in
                                   coe
                                     (coe
                                        seq (coe v8)
                                        (let v9
                                               = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                      (coe v0))
                                                   (coe v1) in
                                         coe
                                           (coe
                                              seq (coe v9)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v1)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe (0 :: Integer))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                          (coe v0))
                                                       erased)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly-infer
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_3804 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_3804 v0 v1 ~v2 ~v3
                                                      ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3804 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3804 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3804 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_354 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_3846 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_3846 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                           ~v7
  = du_checkElab'45'fallback'45'RApp'45'id_3846 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'id_3846 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_3846 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7 v6
                               (coe MAlonzo.Code.Once.IR.C_id_22) v8 in
                     coe
                       (let v12 = addInt (coe (1 :: Integer)) (coe v9) in
                        coe
                          (let v13
                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                     (coe v2) (coe v2) in
                           coe
                             (case coe v13 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                  -> if coe v14
                                       then coe
                                              seq (coe v15)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v12)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v10) erased)))
                                       else coe
                                              seq (coe v15)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-fst
d_checkElab'45'fallback'45'RApp'45'fst_3916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_3916 v0 v1 v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'fst_3916 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'fst_3916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_3916 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7 v6
                                      (coe MAlonzo.Code.Once.IR.C_fst_44) v8 in
                            coe
                              (let v14 = addInt (coe (1 :: Integer)) (coe v9) in
                               coe
                                 (let v15
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                            (coe v2) (coe v2) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                         -> if coe v16
                                              then coe
                                                     seq (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v13)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v10) erased)))
                                              else coe
                                                     seq (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-snd
d_checkElab'45'fallback'45'RApp'45'snd_3986 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_3986 v0 v1 v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'snd_3986 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'snd_3986 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_3986 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7 v6
                                      (coe MAlonzo.Code.Once.IR.C_snd_50) v8 in
                            coe
                              (let v14 = addInt (coe (1 :: Integer)) (coe v9) in
                               coe
                                 (let v15
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                            (coe v2) (coe v2) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                         -> if coe v16
                                              then coe
                                                     seq (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v13)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe v10) erased)))
                                              else coe
                                                     seq (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkViewBridge
d_checkViewBridge_4048 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_4048 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_4072 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_4072 v0 v1 v2 v3 ~v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'generic_4072 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'generic_4072 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_4072 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_2118
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
                 (coe v1)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v3) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then coe
                                        seq (coe v14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11) erased)))
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic-eff
d_checkElab'45'fallback'45'RApp'45'generic'45'eff_4160 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic'45'eff_4160 v0 v1 v2 v3
                                                       v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4160
      v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4160 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4160 v0 v1 v2 v3
                                                        v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_2118
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
                 (coe v1)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240 (coe v3)
                                  (coe v3))
                               (coe
                                  MAlonzo.Code.Once.Type.d__'8799'k__100
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34)))
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240 (coe v4)
                                  (coe v4)) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> coe
                                 seq (coe v14)
                                 (case coe v15 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                      -> let v17
                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                   (coe v3) (coe v3) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                      (coe v4) (coe v4) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                   -> if coe v19
                                                        then coe
                                                               seq (coe v20)
                                                               (case coe v18 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                    -> if coe v21
                                                                         then case coe v22 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                          v10)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v11)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v12)
                                                                                             erased))
                                                                                _ -> coe
                                                                                       seq (coe v21)
                                                                                       (coe
                                                                                          seq
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                         else (case coe v22 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                   -> coe
                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                 _ -> coe
                                                                                        seq
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        else coe
                                                               seq (coe v20)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id-eff
d_checkElab'45'fallback'45'RApp'45'id'45'eff_4302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id'45'eff_4302 v0 v1 v2 v3 ~v4
                                                  ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'id'45'eff_4302 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'id'45'eff_4302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id'45'eff_4302 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_id_22) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (let v14
                                 = coe
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                        (coe v2) (coe v2))
                                     (coe
                                        MAlonzo.Code.Once.Type.d__'8799'k__100
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_eff_36))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                        (coe v3) (coe v3)) in
                           coe
                             (case coe v14 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                  -> coe
                                       seq (coe v15)
                                       (case coe v16 of
                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                            -> let v18
                                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                         (coe v2) (coe v2) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                            (coe v3) (coe v3) in
                                                  coe
                                                    (case coe v18 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                         -> if coe v20
                                                              then coe
                                                                     seq (coe v21)
                                                                     (case coe v19 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                          -> if coe v22
                                                                               then case coe v23 of
                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                v12)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                (coe
                                                                                                   v13)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      v11)
                                                                                                   erased))
                                                                                      _ -> coe
                                                                                             seq
                                                                                             (coe
                                                                                                v22)
                                                                                             (coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v23)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                               else (case coe v23 of
                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                         -> coe
                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                       _ -> coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v23)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                              else coe
                                                                     seq (coe v21)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-fst-eff
d_checkElab'45'fallback'45'RApp'45'fst'45'eff_4412 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst'45'eff_4412 v0 v1 v2 v3 ~v4
                                                   ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4412 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4412 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4412 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                         -> let v14
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v8 v7
                                      (coe MAlonzo.Code.Once.IR.C_fst_44) v9 in
                            coe
                              (let v15 = addInt (coe (1 :: Integer)) (coe v10) in
                               coe
                                 (let v16
                                        = coe
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v2) (coe v2))
                                            (coe
                                               MAlonzo.Code.Once.Type.d__'8799'k__100
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_eff_36))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v3) (coe v3)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                         -> coe
                                              seq (coe v17)
                                              (case coe v18 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                   -> let v20
                                                            = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                (coe v2) (coe v2) in
                                                      coe
                                                        (let v21
                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                   (coe v3) (coe v3) in
                                                         coe
                                                           (case coe v20 of
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                -> if coe v22
                                                                     then coe
                                                                            seq (coe v23)
                                                                            (case coe v21 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                 -> if coe v24
                                                                                      then case coe
                                                                                                  v25 of
                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v11)
                                                                                                          erased))
                                                                                             _ -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v24)
                                                                                                    (coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                      else (case coe
                                                                                                   v25 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                -> coe
                                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                              _ -> coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v24)
                                                                                                     (coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     else coe
                                                                            seq (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-snd-eff
d_checkElab'45'fallback'45'RApp'45'snd'45'eff_4522 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd'45'eff_4522 v0 v1 v2 v3 ~v4
                                                   ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4522 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4522 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4522 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                         -> let v14
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v8 v7
                                      (coe MAlonzo.Code.Once.IR.C_snd_50) v9 in
                            coe
                              (let v15 = addInt (coe (1 :: Integer)) (coe v10) in
                               coe
                                 (let v16
                                        = coe
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v2) (coe v2))
                                            (coe
                                               MAlonzo.Code.Once.Type.d__'8799'k__100
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_eff_36))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                               (coe v3) (coe v3)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                         -> coe
                                              seq (coe v17)
                                              (case coe v18 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                   -> let v20
                                                            = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                (coe v2) (coe v2) in
                                                      coe
                                                        (let v21
                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                   (coe v3) (coe v3) in
                                                         coe
                                                           (case coe v20 of
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                -> if coe v22
                                                                     then coe
                                                                            seq (coe v23)
                                                                            (case coe v21 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                 -> if coe v24
                                                                                      then case coe
                                                                                                  v25 of
                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v11)
                                                                                                          erased))
                                                                                             _ -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v24)
                                                                                                    (coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                      else (case coe
                                                                                                   v25 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                -> coe
                                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                              _ -> coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v24)
                                                                                                     (coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     else coe
                                                                            seq (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-eff
d_checkElab'45'fallback'45'RVar'45'eff_4632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'eff_4632 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8
  = du_checkElab'45'fallback'45'RVar'45'eff_4632 v0 v1 v2 v3
du_checkElab'45'fallback'45'RVar'45'eff_4632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'eff_4632 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v4 ->
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
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then let v7
                           = seq
                               (coe v6)
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
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> case coe v8 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v10 v11 v12 v13 v14
                                   -> let v15
                                            = coe
                                                MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                   (coe v2) (coe v2))
                                                (coe
                                                   MAlonzo.Code.Once.Type.d__'8799'k__100
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                   (coe v3) (coe v3)) in
                                      coe
                                        (case coe v15 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                             -> coe
                                                  seq (coe v16)
                                                  (case coe v17 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                       -> let v19
                                                                = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                    (coe v2) (coe v2) in
                                                          coe
                                                            (let v20
                                                                   = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                       (coe v3) (coe v3) in
                                                             coe
                                                               (case coe v19 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                    -> if coe v21
                                                                         then coe
                                                                                seq (coe v22)
                                                                                (case coe v20 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                     -> if coe v23
                                                                                          then case coe
                                                                                                      v24 of
                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                   -> coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                           v12)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           (coe
                                                                                                              v13)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                              (coe
                                                                                                                 v14)
                                                                                                              erased))
                                                                                                 _ -> coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v23)
                                                                                                        (coe
                                                                                                           seq
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                          else (case coe
                                                                                                       v24 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                  _ -> coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v23)
                                                                                                         (coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v24)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                         else coe
                                                                                seq (coe v22)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v7
                            = seq
                                (coe v6)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2088
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
                        (case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v10 v11 v12 v13 v14
                                    -> let v15
                                             = coe
                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                    (coe v2) (coe v2))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.d__'8799'k__100
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                    (coe v3) (coe v3)) in
                                       coe
                                         (case coe v15 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                              -> coe
                                                   seq (coe v16)
                                                   (case coe v17 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> let v19
                                                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                     (coe v2) (coe v2) in
                                                           coe
                                                             (let v20
                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                        (coe v3) (coe v3) in
                                                              coe
                                                                (case coe v19 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                     -> if coe v21
                                                                          then coe
                                                                                 seq (coe v22)
                                                                                 (case coe v20 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                      -> if coe v23
                                                                                           then case coe
                                                                                                       v24 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v25
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                            v12)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               v13)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v14)
                                                                                                               erased))
                                                                                                  _ -> coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v23)
                                                                                                         (coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v24)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                           else (case coe
                                                                                                        v24 of
                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                     -> coe
                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                   _ -> coe
                                                                                                          seq
                                                                                                          (coe
                                                                                                             v23)
                                                                                                          (coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v24)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          else coe
                                                                                 seq (coe v22)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-initial-eff
d_checkElab'45'fallback'45'RApp'45'initial'45'eff_4740 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'initial'45'eff_4740 v0 v1 ~v2
                                                       ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4740 v0 v1
du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4740 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4740 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1844
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_124) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v5
                          (coe MAlonzo.Code.Once.Type.C_Void_124)
                          (coe MAlonzo.Code.Once.IR.C_initial_78) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-eff
d_checkElab'45'fallback'45'RApp'45'apply'45'eff_4784 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'eff_4784 v0 v1 v2 v3
                                                     ~v4 ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4784 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4784 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4784 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                       -> case coe v17 of
                                            MAlonzo.Code.Once.Type.C_Zero_6
                                              -> let v19
                                                       = seq
                                                           (coe v18)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                                    (coe
                                                                       ("apply"
                                                                        ::
                                                                        Data.Text.Text))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                 coe
                                                   (case coe v19 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                        -> case coe v20 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v22 v23 v24 v25 v26
                                                               -> let v27
                                                                        = coe
                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                               (coe v2) (coe v2))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d__'8799'k__100
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_eff_36))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_pure_34)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                               (coe v3) (coe v3)) in
                                                                  coe
                                                                    (case coe v27 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                         -> coe
                                                                              seq (coe v28)
                                                                              (case coe v29 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                   -> let v31
                                                                                            = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   v2) in
                                                                                      coe
                                                                                        (let v32
                                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v3) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v31 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                -> if coe
                                                                                                        v33
                                                                                                     then coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v34)
                                                                                                            (case coe
                                                                                                                    v32 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                                                                 -> if coe
                                                                                                                         v35
                                                                                                                      then case coe
                                                                                                                                  v36 of
                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v37
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                                                       v24)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                          (coe
                                                                                                                                             v26)
                                                                                                                                          erased))
                                                                                                                             _ -> coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v35)
                                                                                                                                    (coe
                                                                                                                                       seq
                                                                                                                                       (coe
                                                                                                                                          v36)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                      else (case coe
                                                                                                                                   v36 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                              _ -> coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v35)
                                                                                                                                     (coe
                                                                                                                                        seq
                                                                                                                                        (coe
                                                                                                                                           v36)
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                     else coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v34)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_One_8
                                              -> let v19
                                                       = seq
                                                           (coe v18)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                                    (coe
                                                                       ("apply"
                                                                        ::
                                                                        Data.Text.Text))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                 coe
                                                   (case coe v19 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                        -> case coe v20 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v22 v23 v24 v25 v26
                                                               -> let v27
                                                                        = coe
                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                               (coe v2) (coe v2))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d__'8799'k__100
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_eff_36))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_pure_34)))
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                               (coe v3) (coe v3)) in
                                                                  coe
                                                                    (case coe v27 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                         -> coe
                                                                              seq (coe v28)
                                                                              (case coe v29 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                   -> let v31
                                                                                            = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   v2) in
                                                                                      coe
                                                                                        (let v32
                                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v3) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v31 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                -> if coe
                                                                                                        v33
                                                                                                     then coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v34)
                                                                                                            (case coe
                                                                                                                    v32 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                                                                 -> if coe
                                                                                                                         v35
                                                                                                                      then case coe
                                                                                                                                  v36 of
                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v37
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                                                       v24)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                          (coe
                                                                                                                                             v26)
                                                                                                                                          erased))
                                                                                                                             _ -> coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v35)
                                                                                                                                    (coe
                                                                                                                                       seq
                                                                                                                                       (coe
                                                                                                                                          v36)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                      else (case coe
                                                                                                                                   v36 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                              _ -> coe
                                                                                                                                     seq
                                                                                                                                     (coe
                                                                                                                                        v35)
                                                                                                                                     (coe
                                                                                                                                        seq
                                                                                                                                        (coe
                                                                                                                                           v36)
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                     else coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v34)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                              (coe v14) (coe v13) in
                                                    coe
                                                      (case coe v19 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                           -> if coe v20
                                                                then let v22
                                                                           = seq
                                                                               (coe v21)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316
                                                                                     (coe v16)
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
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              v8)))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378
                                                                                        v8
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C__'42'__126
                                                                                           (coe v12)
                                                                                           (coe
                                                                                              v14))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.IR.C_apply_92)
                                                                                        v9)
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe v10))
                                                                                     (coe v11))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_278
                                                                                     v14 v8 v6)) in
                                                                     coe
                                                                       (case coe v22 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                            -> case coe v23 of
                                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v25 v26 v27 v28 v29
                                                                                   -> let v30
                                                                                            = coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                   (coe
                                                                                                      v2)
                                                                                                   (coe
                                                                                                      v2))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.d__'8799'k__100
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                      (coe
                                                                                                         v17)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Type.C_eff_36))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                      (coe
                                                                                                         v17)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Type.C_pure_34)))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v3)) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v30 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                             -> coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v31)
                                                                                                  (case coe
                                                                                                          v32 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                       -> let v34
                                                                                                                = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                                    (coe
                                                                                                                       v2)
                                                                                                                    (coe
                                                                                                                       v2) in
                                                                                                          coe
                                                                                                            (let v35
                                                                                                                   = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                                       (coe
                                                                                                                          v3)
                                                                                                                       (coe
                                                                                                                          v3) in
                                                                                                             coe
                                                                                                               (case coe
                                                                                                                       v34 of
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v36 v37
                                                                                                                    -> if coe
                                                                                                                            v36
                                                                                                                         then coe
                                                                                                                                seq
                                                                                                                                (coe
                                                                                                                                   v37)
                                                                                                                                (case coe
                                                                                                                                        v35 of
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                                                     -> if coe
                                                                                                                                             v38
                                                                                                                                          then case coe
                                                                                                                                                      v39 of
                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v40
                                                                                                                                                   -> coe
                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                                                                           v27)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                           (coe
                                                                                                                                                              v28)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                              (coe
                                                                                                                                                                 v29)
                                                                                                                                                              erased))
                                                                                                                                                 _ -> coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v38)
                                                                                                                                                        (coe
                                                                                                                                                           seq
                                                                                                                                                           (coe
                                                                                                                                                              v39)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                                          else (case coe
                                                                                                                                                       v39 of
                                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                                    -> coe
                                                                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                                                  _ -> coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v38)
                                                                                                                                                         (coe
                                                                                                                                                            seq
                                                                                                                                                            (coe
                                                                                                                                                               v39)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                         else coe
                                                                                                                                seq
                                                                                                                                (coe
                                                                                                                                   v37)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                else (let v22
                                                                            = seq
                                                                                (coe v21)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_84
                                                                                         (coe
                                                                                            ("apply"
                                                                                             ::
                                                                                             Data.Text.Text))))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                      coe
                                                                        (case coe v22 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                             -> case coe v23 of
                                                                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v25 v26 v27 v28 v29
                                                                                    -> let v30
                                                                                             = coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                    (coe
                                                                                                       v2)
                                                                                                    (coe
                                                                                                       v2))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Type.d__'8799'k__100
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                       (coe
                                                                                                          v17)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Type.C_eff_36))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                       (coe
                                                                                                          v17)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Type.C_pure_34)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v3)) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v30 of
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v31)
                                                                                                   (case coe
                                                                                                           v32 of
                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                        -> let v34
                                                                                                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                                     (coe
                                                                                                                        v2)
                                                                                                                     (coe
                                                                                                                        v2) in
                                                                                                           coe
                                                                                                             (let v35
                                                                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                                                                                                        (coe
                                                                                                                           v3)
                                                                                                                        (coe
                                                                                                                           v3) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v34 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v36 v37
                                                                                                                     -> if coe
                                                                                                                             v36
                                                                                                                          then coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v37)
                                                                                                                                 (case coe
                                                                                                                                         v35 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                                                      -> if coe
                                                                                                                                              v38
                                                                                                                                           then case coe
                                                                                                                                                       v39 of
                                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v40
                                                                                                                                                    -> coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Once.Surface.Syntax.C_arr''_328
                                                                                                                                                            v27)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                            (coe
                                                                                                                                                               v28)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                               (coe
                                                                                                                                                                  v29)
                                                                                                                                                               erased))
                                                                                                                                                  _ -> coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v38)
                                                                                                                                                         (coe
                                                                                                                                                            seq
                                                                                                                                                            (coe
                                                                                                                                                               v39)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                                           else (case coe
                                                                                                                                                        v39 of
                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                                                   _ -> coe
                                                                                                                                                          seq
                                                                                                                                                          (coe
                                                                                                                                                             v38)
                                                                                                                                                          (coe
                                                                                                                                                             seq
                                                                                                                                                             (coe
                                                                                                                                                                v39)
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                          else coe
                                                                                                                                 seq
                                                                                                                                 (coe
                                                                                                                                    v37)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.cata-go-canonical
d_cata'45'go'45'canonical_4886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_4886 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_4900 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_4900 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_4934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'just'45'success_4934 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_5024 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_5024 = erased
-- Once.TypeCheck.ElaborateProofs.extract-morph-eff-cata
d_extract'45'morph'45'eff'45'cata_5102 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extract'45'morph'45'eff'45'cata_5102 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_5136 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_5136 v0 v1 v2 ~v3 ~v4
                                                 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'terminal_5136 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'terminal_5136 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_5136 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v6 v7 v8 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_378 v7 v6
                               (coe MAlonzo.Code.Once.IR.C_terminal_74) v8 in
                     coe
                       (let v12 = addInt (coe (1 :: Integer)) (coe v9) in
                        coe
                          (let v13
                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                                     (coe v2) (coe v2) in
                           coe
                             (case coe v13 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                  -> if coe v14
                                       then coe
                                              seq (coe v15)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v12)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v10) erased)))
                                       else coe
                                              seq (coe v15)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RBinOp
d_checkElab'45'fallback'45'RBinOp_5210 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_5210 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9
  = du_checkElab'45'fallback'45'RBinOp_5210 v0 v1 v2 v3
du_checkElab'45'fallback'45'RBinOp_5210 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_5210 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_1884
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__240
                               (coe v7) (coe v7) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then coe
                                        seq (coe v14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v11) erased)))
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExprTyped
d_compileExprTyped_5364 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_5364 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1844
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370) (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_340 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate'45'default_336
                   (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) v1 v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_342 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExpr
d_compileExpr_5388 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_5388 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370)
                 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_316 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate'45'default_336
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) v2 v4))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_318 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferElabProj
d_inferElabProj_5410 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_302
d_inferElabProj_5410 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1828 (coe v0)
         (coe v1))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_5426 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_326
d_checkElabProj_5426 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1836 (coe v0)
         (coe v1) (coe v2))
