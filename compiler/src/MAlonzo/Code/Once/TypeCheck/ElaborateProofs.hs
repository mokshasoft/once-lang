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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
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
d_checkElab'45'fallback'45'RFloat_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3 ~v4
  = du_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3
du_checkElab'45'fallback'45'RFloat_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_float_198
         (coe
            MAlonzo.Code.Once.Float.Decimal.C__'47'10'94'__16
            (coe
               addInt
               (coe
                  mulInt (coe v1)
                  (coe
                     MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                     (coe v3)))
               (coe v2))
            (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RStringLit
d_checkElab'45'fallback'45'RStringLit_100 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RStringLit_100 v0 v1
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
d_checkElab'45'fallback'45'RUnit_128 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_128 v0
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
d_checkElab'45'fallback'45'RQualified_164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_164 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8
  = du_checkElab'45'fallback'45'RQualified_164 v0 v1 v2
du_checkElab'45'fallback'45'RQualified_164 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_164 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_2256
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RResolved_322 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RResolved_322 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7
  = du_checkElab'45'fallback'45'RResolved_322 v0 v1
du_checkElab'45'fallback'45'RResolved_322 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_322 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RResolved'45'aux_2264
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
                  -> let v10
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RAnnot_466 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_466 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RAnnot_466 v0 v1 v2
du_checkElab'45'fallback'45'RAnnot_466 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_466 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2064
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
                 (coe v0) (coe v1) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RLet_614 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_614 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkElab'45'fallback'45'RLet_614 v0 v1 v2 v3
du_checkElab'45'fallback'45'RLet_614 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_614 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_2140
              (coe v0) (coe v1) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RDestruct_794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_794 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                         ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RDestruct_794 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RDestruct_794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_794 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_2176
              (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v9 v10 v11 v12 v13
                  -> let v14
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RUnaryOp_996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_996 v0 ~v1 v2 v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_996 v0 v2 v3
du_checkElab'45'fallback'45'RUnaryOp_996 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_996 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_350
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_332
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_184
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v5)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_342
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_198
                          (coe
                             MAlonzo.Code.Once.Float.Decimal.C__'47'10'94'__16
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d_'45'__260
                                (coe
                                   addInt
                                   (coe
                                      mulInt (coe v8)
                                      (coe
                                         MAlonzo.Code.Data.Nat.Base.d__'94'__276
                                         (coe (10 :: Integer)) (coe v10)))
                                   (coe v9)))
                             (coe v10)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_346
           -> let v5
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_2070
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                           (coe v1)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v8 v9 v10 v11 v12
                            -> let v13
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                         (coe v2) (coe v2) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                      -> if coe v14
                                           then coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v10)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) erased)))
                                           else coe
                                                  seq (coe v15)
                                                  (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_1204 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_1204 v0
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
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_1228 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_1228 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-bridge
d_inferElabV'45'RVar'45'poly'45'bridge_1240 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'bridge_1240 = erased
-- Once.TypeCheck.ElaborateProofs._.helper
d_helper_1290 ::
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
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_1290 = erased
-- Once.TypeCheck.ElaborateProofs._.bridge-eq
d_bridge'45'eq_1292 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'eq_1292 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-eq
d_inferElabV'45'RVar'45'poly'45'aux'45'eq_1302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_BareBuiltinClass_1272 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'eq_1302 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_1316 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_1316 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_1332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_1332 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_1344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_1344
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_1362 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_1362
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_1386 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_1386 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-fail-bridge
d_inferElabV'45'RVar'45'fail'45'bridge_1412 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'fail'45'bridge_1412 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_1436 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_1436 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'id_1436 v0 v1
du_checkElab'45'fallback'45'RVar'45'id_1436 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_1436 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_just'8802'nothing_1510 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_LookupImportView_632 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1510 = erased
-- Once.TypeCheck.ElaborateProofs._.just≢nothing
d_just'8802'nothing_1530 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_LookupLocalView_582 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_1530 = erased
-- Once.TypeCheck.ElaborateProofs.just≢nothing-Maybe
d_just'8802'nothing'45'Maybe_1536 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_1536 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_1550 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_1550 v0 v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'fst_1550 v0 v1
du_checkElab'45'fallback'45'RVar'45'fst_1550 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_1550 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkElab'45'fallback'45'RVar'45'snd_1652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_1652 v0 ~v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'snd_1652 v0 v2
du_checkElab'45'fallback'45'RVar'45'snd_1652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_1652 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkElab'45'fallback'45'RVar'45'terminal_1754 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_1754 v0 ~v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'terminal_1754 v0
du_checkElab'45'fallback'45'RVar'45'terminal_1754 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_1754 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkElab'45'fallback'45'RVar'45'terminalV_1822 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_1822 v0 ~v1 ~v2 ~v3
                                                  ~v4
  = du_checkElab'45'fallback'45'RVar'45'terminalV_1822 v0
du_checkElab'45'fallback'45'RVar'45'terminalV_1822 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_1822 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484))
                                                erased)))
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_1886 v0 ~v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'initial_1886 v0
du_checkElab'45'fallback'45'RVar'45'initial_1886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_1886 v0
  = let v1
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkElab'45'fallback'45'RVar'45'inl_1952 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_1952 v0 v1 ~v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inl_1952 v0 v1
du_checkElab'45'fallback'45'RVar'45'inl_1952 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_1952 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkElab'45'fallback'45'RVar'45'inr_2054 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_2054 v0 ~v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inr_2054 v0 v2
du_checkElab'45'fallback'45'RVar'45'inr_2054 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_2054 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_checkInGo'45'J_2154 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2154 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_2186 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_2186 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkInGo'45'just'45'success_2186 v0 v1 v2 v3
du_checkInGo'45'just'45'success_2186 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_2186 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2)
                 (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v7 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7
                          (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                             (coe v2) (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2)))
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
d_checkElab'45'fallback'45'RApp'45'In_2238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_2238 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'In_2238 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'In_2238 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_2238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_2186 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_2186 (coe v0) (coe v1) (coe v2)
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
                        du_checkInGo'45'just'45'success_2186 (coe v0) (coe v1) (coe v2)
                        (coe v3)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_2276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_2276 v0 v1 v2 v3 ~v4 ~v5
                                              ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply_2276 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply_2276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_2276 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                       -> coe
                                            seq (coe v17)
                                            (coe
                                               seq (coe v18)
                                               (let v19
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v19 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                       -> if coe v20
                                                            then coe
                                                                   seq (coe v21)
                                                                   (let v22
                                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                                             v8
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
d_resolveExprWF_2364 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExprWF_2364 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_resolveExprWF_2364 v0 v1 v3 v4 v6 v7 v8 v9
du_resolveExprWF_2364 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExprWF_2364 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_16 v10
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v11 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v11
                    (coe
                       du_resolveExprWF_2364 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v17))
                       (coe v19) (coe v3) (coe v4) (coe v5) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_48 v10 v11 v12 v14
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v14)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v15))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v10 v11 v12 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v10 v11 v12
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v18))
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v10 v11
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1) (coe v16) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v14))
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1) (coe v17) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v12
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v12))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v11 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v11) (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_112
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_124
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1) (coe v15) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v10 v11 v12 v13 v14 v15 v16 v18 v19 v20
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v10 v11 v12 v13 v14
             v15 v16
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v15) (coe v16))
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v18))
             (coe
                du_resolveExprWF_2364 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v19))
             (coe
                du_resolveExprWF_2364 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v16))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v20))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_162
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v10 v11 v12 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v10 v11 v12 v13
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v15))
             (coe
                du_resolveExprWF_2364 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v13))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v10
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v10
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_198 v10
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_208 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_286 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_304
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_324 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v10 v11
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v12))
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                    (coe
                       du_resolveExprWF_2364 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v14) (coe v16))
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v11 v12
        -> let v13
                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                     (coe v5)
                     (coe
                        MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v11)) in
           coe
             (case coe v13 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                  -> coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closure_392
                       (MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v11))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v11 v12
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v11
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v10
        -> coe
             du_resolvePolyCase_2378 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v10) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48 (coe v3)
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414 v13
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414 v13
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v10 v11 v13
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1) (coe v11) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_438 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_438 v13
                                  (coe
                                     du_resolveExprWF_2364 (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v18)
                                           (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                        (coe v17))
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_450 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v20
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_ana_450 v13
                                  (coe
                                     du_resolveExprWF_2364 (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v20)
                                           (coe v15)))
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolvePolyCase
d_resolvePolyCase_2378 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvePolyCase_2378 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_resolvePolyCase_2378 v0 v1 v2 v4 v5 v6 v7 v8 v9
du_resolvePolyCase_2378 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvePolyCase_2378 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    du_applySplice_2394 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1872
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v6)
                             (coe v2)))
                       (coe v11) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.applySplice
d_applySplice_2394 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_applySplice_2394 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 ~v10 ~v11 v12
  = du_applySplice_2394 v0 v1 v2 v4 v5 v6 v7 v8 v12
du_applySplice_2394 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_applySplice_2394 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v9 v10 v11 v12
        -> coe
             seq (coe v9)
             (coe
                du_resolveExprWF_2364 (coe v0) (coe v1) (coe v7)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v6)
                   (coe v2))
                (coe v3) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1208 (coe v1)
                   (coe v7) (coe v10)))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_3000 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExpr_3000 v0 v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_resolveExpr_3000 v0 v1 v3 v4 v5 v6 v7 v8
du_resolveExpr_3000 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExpr_3000 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_resolveExprWF_2364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_3026 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_3026 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_3054 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_3054 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_3082 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_3082 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_3108 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_3108 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_3134 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_3134 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_3156 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_3156 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_3178 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_3178 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_3200 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_3200 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_3222 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_3222 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_3258 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_3258 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_3272 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_3272 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_3292 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_3292 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_3320 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_3320 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_3336 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_3336 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-str
d_resolveExpr'45'str_3352 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'str_3352 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_3374 ::
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
d_resolveExpr'45'add_3374 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_3396 ::
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
d_resolveExpr'45'sub_3396 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_3418 ::
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
d_resolveExpr'45'mul_3418 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_3440 ::
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
d_resolveExpr'45'div_3440 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_3462 ::
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
d_resolveExpr'45'mod''_3462 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_3480 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_3480 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_3502 ::
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
d_resolveExpr'45'lt_3502 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_3524 ::
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
d_resolveExpr'45'le_3524 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_3546 ::
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
d_resolveExpr'45'gt_3546 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_3568 ::
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
d_resolveExpr'45'ge_3568 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_3590 ::
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
d_resolveExpr'45'eq_3590 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_3612 ::
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
d_resolveExpr'45'ne_3612 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-arr'
d_resolveExpr'45'arr''_3634 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'arr''_3634 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_3654 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp'45'extern_3654 = erased
-- Once.TypeCheck.ElaborateProofs.acc-step-at-poly
d_acc'45'step'45'at'45'poly_3670 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_acc'45'step'45'at'45'poly_3670 = erased
-- Once.TypeCheck.ElaborateProofs.applySplice-eq-irrel
d_applySplice'45'eq'45'irrel_3708 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applySplice'45'eq'45'irrel_3708 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-poly-match
d_resolveExpr'45'poly'45'match_3776 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'poly'45'match_3776 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_3824 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
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
d_checkElab'45'fallback'45'RVar'45'poly_3824 v0 v1 ~v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RVar'45'poly_3824 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly_3824 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_3824 v0 v1
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
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
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
                                                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
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
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                                    MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
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
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
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
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926 v0 v1 ~v2 ~v3
                                                      ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_3968 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_3968 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                           ~v7
  = du_checkElab'45'fallback'45'RApp'45'id_3968 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'id_3968 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_3968 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7 v6
                               (coe MAlonzo.Code.Once.IR.C_id_22) v8 in
                     coe
                       (let v12 = addInt (coe (1 :: Integer)) (coe v9) in
                        coe
                          (let v13
                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RApp'45'fst_4038 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_4038 v0 v1 v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'fst_4038 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'fst_4038 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_4038 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7 v6
                                      (coe MAlonzo.Code.Once.IR.C_fst_44) v8 in
                            coe
                              (let v14 = addInt (coe (1 :: Integer)) (coe v9) in
                               coe
                                 (let v15
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RApp'45'snd_4108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_4108 v0 v1 v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'snd_4108 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'snd_4108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_4108 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7 v6
                                      (coe MAlonzo.Code.Once.IR.C_snd_50) v8 in
                            coe
                              (let v14 = addInt (coe (1 :: Integer)) (coe v9) in
                               coe
                                 (let v15
                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkViewBridge_4170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_4170 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_4194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_4194 v0 v1 v2 v3 ~v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'generic_4194 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'generic_4194 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_4194 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_2364
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
                 (coe v1)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282 v0 v1 v2 v3
                                                       v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282
      v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282 v0 v1 v2 v3
                                                        v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_2364
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1062
                 (coe v1)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v8 v9 v10 v11 v12
                  -> coe
                       seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                       (let v13
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                  (coe v3) (coe v3) in
                        coe
                          (case coe v13 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                               -> if coe v14
                                    then coe
                                           seq (coe v15)
                                           (let v16
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                      (coe v4) (coe v4) in
                                            coe
                                              (case coe v16 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                   -> if coe v17
                                                        then case coe v18 of
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                 -> coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                         v10)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v11)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v12) erased))
                                                               _ -> coe
                                                                      seq (coe v17)
                                                                      (coe
                                                                         seq (coe v18)
                                                                         (coe
                                                                            MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                        else (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                  -> coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                _ -> coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          seq (coe v18)
                                                                          (coe
                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                    else coe
                                           seq (coe v15)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id-eff
d_checkElab'45'fallback'45'RApp'45'id'45'eff_4424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id'45'eff_4424 v0 v1 v2 v3 ~v4
                                                  ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'id'45'eff_4424 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'id'45'eff_4424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id'45'eff_4424 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_id_22) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (coe
                             seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                             (let v14
                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                        (coe v2) (coe v2) in
                              coe
                                (case coe v14 of
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                     -> if coe v15
                                          then coe
                                                 seq (coe v16)
                                                 (let v17
                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                            (coe v3) (coe v3) in
                                                  coe
                                                    (case coe v17 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                         -> if coe v18
                                                              then case coe v19 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                       -> coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                               v12)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe v13)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v11) erased))
                                                                     _ -> coe
                                                                            seq (coe v18)
                                                                            (coe
                                                                               seq (coe v19)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                              else (case coe v19 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                        -> coe
                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                      _ -> coe
                                                                             seq (coe v18)
                                                                             (coe
                                                                                seq (coe v19)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                          else coe
                                                 seq (coe v16)
                                                 (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                   _ -> MAlonzo.RTE.mazUnreachableError))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-fst-eff
d_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534 v0 v1 v2 v3 ~v4
                                                   ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> coe
                       seq (coe v7)
                       (let v12
                              = coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_fst_44) v9 in
                        coe
                          (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                           coe
                             (coe
                                seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                (let v14
                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                           (coe v2) (coe v2) in
                                 coe
                                   (case coe v14 of
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                        -> if coe v15
                                             then coe
                                                    seq (coe v16)
                                                    (let v17
                                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                               (coe v3) (coe v3) in
                                                     coe
                                                       (case coe v17 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                            -> if coe v18
                                                                 then case coe v19 of
                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                  v12)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v11)
                                                                                     erased))
                                                                        _ -> coe
                                                                               seq (coe v18)
                                                                               (coe
                                                                                  seq (coe v19)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                 else (case coe v19 of
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                           -> coe
                                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                         _ -> coe
                                                                                seq (coe v18)
                                                                                (coe
                                                                                   seq (coe v19)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                             else coe
                                                    seq (coe v16)
                                                    (coe
                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                      _ -> MAlonzo.RTE.mazUnreachableError)))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-snd-eff
d_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644 v0 v1 v2 v3 ~v4
                                                   ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> coe
                       seq (coe v7)
                       (let v12
                              = coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                  (coe MAlonzo.Code.Once.IR.C_snd_50) v9 in
                        coe
                          (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                           coe
                             (coe
                                seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                (let v14
                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                           (coe v2) (coe v2) in
                                 coe
                                   (case coe v14 of
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                        -> if coe v15
                                             then coe
                                                    seq (coe v16)
                                                    (let v17
                                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                               (coe v3) (coe v3) in
                                                     coe
                                                       (case coe v17 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                            -> if coe v18
                                                                 then case coe v19 of
                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                  v12)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v11)
                                                                                     erased))
                                                                        _ -> coe
                                                                               seq (coe v18)
                                                                               (coe
                                                                                  seq (coe v19)
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                 else (case coe v19 of
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                           -> coe
                                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                         _ -> coe
                                                                                seq (coe v18)
                                                                                (coe
                                                                                   seq (coe v19)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                             else coe
                                                    seq (coe v16)
                                                    (coe
                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                      _ -> MAlonzo.RTE.mazUnreachableError)))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-eff
d_checkElab'45'fallback'45'RVar'45'eff_4754 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'eff_4754 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8
  = du_checkElab'45'fallback'45'RVar'45'eff_4754 v0 v1 v2 v3
du_checkElab'45'fallback'45'RVar'45'eff_4754 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'eff_4754 v0 v1 v2 v3
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
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
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
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                   -> coe
                                        seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                        (let v15
                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v2) (coe v2) in
                                         coe
                                           (case coe v15 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                -> if coe v16
                                                     then coe
                                                            seq (coe v17)
                                                            (let v18
                                                                   = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                       (coe v3) (coe v3) in
                                                             coe
                                                               (case coe v18 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                    -> if coe v19
                                                                         then case coe v20 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                          v12)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v14)
                                                                                             erased))
                                                                                _ -> coe
                                                                                       seq (coe v19)
                                                                                       (coe
                                                                                          seq
                                                                                          (coe v20)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                         else (case coe v20 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                   -> coe
                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                 _ -> coe
                                                                                        seq
                                                                                        (coe v19)
                                                                                        (coe
                                                                                           seq
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     else coe
                                                            seq (coe v17)
                                                            (coe
                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v7
                            = seq
                                (coe v6)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                    -> coe
                                         seq (coe v5)
                                         (let v15
                                                = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                    (coe v2) (coe v2) in
                                          coe
                                            (case coe v15 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                 -> if coe v16
                                                      then coe
                                                             seq (coe v17)
                                                             (let v18
                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                        (coe v3) (coe v3) in
                                                              coe
                                                                (case coe v18 of
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                     -> if coe v19
                                                                          then case coe v20 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                           v12)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v13)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 v14)
                                                                                              erased))
                                                                                 _ -> coe
                                                                                        seq
                                                                                        (coe v19)
                                                                                        (coe
                                                                                           seq
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                          else (case coe v20 of
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                    -> coe
                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                  _ -> coe
                                                                                         seq
                                                                                         (coe v19)
                                                                                         (coe
                                                                                            seq
                                                                                            (coe
                                                                                               v20)
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                      else coe
                                                             seq (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-initial-eff
d_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862 v0 v1 ~v2
                                                       ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862 v0 v1
du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_120) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v5
                          (coe MAlonzo.Code.Once.Type.C_Void_120)
                          (coe MAlonzo.Code.Once.IR.C_initial_78) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-eff
d_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906 v0 v1 v2 v3
                                                     ~v4 ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
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
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v22 v23 v24 v25 v26
                                                               -> coe
                                                                    seq
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                    (let v27
                                                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                               (coe v2) (coe v2) in
                                                                     coe
                                                                       (case coe v27 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                            -> if coe v28
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v29)
                                                                                        (let v30
                                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v3) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v30 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                -> if coe
                                                                                                        v31
                                                                                                     then case coe
                                                                                                                 v32 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v33
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
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
                                                                                                                      v31)
                                                                                                                   (coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v32)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                     else (case coe
                                                                                                                  v32 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                               -> coe
                                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                             _ -> coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v31)
                                                                                                                    (coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v32)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v29)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_One_8
                                              -> let v19
                                                       = seq
                                                           (coe v18)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v22 v23 v24 v25 v26
                                                               -> coe
                                                                    seq
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                    (let v27
                                                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                               (coe v2) (coe v2) in
                                                                     coe
                                                                       (case coe v27 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                            -> if coe v28
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v29)
                                                                                        (let v30
                                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v3) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v30 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                -> if coe
                                                                                                        v31
                                                                                                     then case coe
                                                                                                                 v32 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v33
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
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
                                                                                                                      v31)
                                                                                                                   (coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v32)
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                     else (case coe
                                                                                                                  v32 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                               -> coe
                                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                             _ -> coe
                                                                                                                    seq
                                                                                                                    (coe
                                                                                                                       v31)
                                                                                                                    (coe
                                                                                                                       seq
                                                                                                                       (coe
                                                                                                                          v32)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v29)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> coe
                                                   seq (coe v18)
                                                   (let v19
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                                     MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                                                                     (coe v16)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                              (coe
                                                                                                 v0)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              v8)))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                                        v8
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C__'42'__122
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
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                                                                                     v14 v8 v6)) in
                                                                     coe
                                                                       (case coe v22 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                                            -> case coe v23 of
                                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v25 v26 v27 v28 v29
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                                        (let v30
                                                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                   (coe
                                                                                                      v2)
                                                                                                   (coe
                                                                                                      v2) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v30 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                -> if coe
                                                                                                        v31
                                                                                                     then coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v32)
                                                                                                            (let v33
                                                                                                                   = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                                       (coe
                                                                                                                          v3)
                                                                                                                       (coe
                                                                                                                          v3) in
                                                                                                             coe
                                                                                                               (case coe
                                                                                                                       v33 of
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                    -> if coe
                                                                                                                            v34
                                                                                                                         then case coe
                                                                                                                                     v35 of
                                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                  -> coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
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
                                                                                                                                          v34)
                                                                                                                                       (coe
                                                                                                                                          seq
                                                                                                                                          (coe
                                                                                                                                             v35)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                         else (case coe
                                                                                                                                      v35 of
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                   -> coe
                                                                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                                 _ -> coe
                                                                                                                                        seq
                                                                                                                                        (coe
                                                                                                                                           v34)
                                                                                                                                        (coe
                                                                                                                                           seq
                                                                                                                                           (coe
                                                                                                                                              v35)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                     else coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v32)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                else (let v22
                                                                            = seq
                                                                                (coe v21)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
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
                                                                                  MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v25 v26 v27 v28 v29
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v20)
                                                                                         (let v30
                                                                                                = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                    (coe
                                                                                                       v2)
                                                                                                    (coe
                                                                                                       v2) in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v30 of
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                 -> if coe
                                                                                                         v31
                                                                                                      then coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v32)
                                                                                                             (let v33
                                                                                                                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                                        (coe
                                                                                                                           v3)
                                                                                                                        (coe
                                                                                                                           v3) in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v33 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                     -> if coe
                                                                                                                             v34
                                                                                                                          then case coe
                                                                                                                                      v35 of
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                   -> coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
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
                                                                                                                                           v34)
                                                                                                                                        (coe
                                                                                                                                           seq
                                                                                                                                           (coe
                                                                                                                                              v35)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                                                          else (case coe
                                                                                                                                       v35 of
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                    -> coe
                                                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                                  _ -> coe
                                                                                                                                         seq
                                                                                                                                         (coe
                                                                                                                                            v34)
                                                                                                                                         (coe
                                                                                                                                            seq
                                                                                                                                            (coe
                                                                                                                                               v35)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                      else coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v32)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
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
d_cata'45'go'45'canonical_5008 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_5008 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_5022 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_5022 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_5056 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
d_checkCataGo'45'just'45'success_5056 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_5146 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_5146 = erased
-- Once.TypeCheck.ElaborateProofs.extract-morph-eff-cata
d_extract'45'morph'45'eff'45'cata_5224 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extract'45'morph'45'eff'45'cata_5224 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_5258 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_5258 v0 v1 v2 ~v3 ~v4
                                                 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'terminal_5258 v0 v1 v2
du_checkElab'45'fallback'45'RApp'45'terminal_5258 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_5258 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7 v6
                               (coe MAlonzo.Code.Once.IR.C_terminal_74) v8 in
                     coe
                       (let v12 = addInt (coe (1 :: Integer)) (coe v9) in
                        coe
                          (let v13
                                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_checkElab'45'fallback'45'RBinOp_5332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_5332 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9
  = du_checkElab'45'fallback'45'RBinOp_5332 v0 v1 v2 v3
du_checkElab'45'fallback'45'RBinOp_5332 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_5332 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_2130
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                 (coe v2))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_compileExprTyped_5486 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_5486 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370) (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate'45'default_374
                   (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) v1 v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExpr
d_compileExpr_5510 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_5510 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_370)
                 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate'45'default_374
                      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) v2 v4))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferElabProj
d_inferElabProj_5532 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_286
d_inferElabProj_5532 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
         (coe v1))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_5548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310
d_checkElabProj_5548 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_2032 (coe v0)
         (coe v1) (coe v2))
