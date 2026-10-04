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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RInt
d_checkElab'45'fallback'45'RInt_16 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
         (coe MAlonzo.Code.Once.Type.C_Int_134)
         (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RFloat
d_checkElab'45'fallback'45'RFloat_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3 ~v4
  = du_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3
du_checkElab'45'fallback'45'RFloat_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_52 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
         (coe MAlonzo.Code.Once.Type.C_Float_136)
         (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_194
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
               (coe v3))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_98 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_98 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
         (coe MAlonzo.Code.Once.Type.C_Unit_120)
         (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RQualified
d_checkElab'45'fallback'45'RQualified_136 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_136 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RQualified_136 v0 v1 v2 v3
du_checkElab'45'fallback'45'RQualified_136 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_136 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_4390
              (coe v0) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_454
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                 (coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("." :: Data.Text.Text) v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v7) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v7
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RResolved
d_checkElab'45'fallback'45'RResolved_324 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RResolved_324 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RResolved_324 v0 v1 v2 v3
du_checkElab'45'fallback'45'RResolved_324 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_324 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1222
              (coe v2) in
    coe
      (let v5
             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'RResolved'45'dispatch_5706
                 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1222
                    (coe v2)) in
       coe
         (coe
            seq (coe v4)
            (case coe v5 of
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                 -> case coe v6 of
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                        -> let v13
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                     (coe v3) (coe v1) in
                           coe
                             (case coe v13 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                  -> if coe v14
                                       then case coe v15 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                        v3 v16 v10)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v15)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RAnnot
d_checkElab'45'fallback'45'RAnnot_1174 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_1174 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9
  = du_checkElab'45'fallback'45'RAnnot_1174 v0 v1 v2 v3
du_checkElab'45'fallback'45'RAnnot_1174 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_1174 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2718
              (coe v3)
              (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v3))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172 (coe v0)
                 (coe v2) (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RLet
d_checkElab'45'fallback'45'RLet_1352 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_1352 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8
                                     ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RLet_1352 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RLet_1352 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_1352 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6218
              (coe v0) (coe v2) (coe v4)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v8) (coe v1) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v8
                                                  v16 v10)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v15)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RDestruct
d_checkElab'45'fallback'45'RDestruct_1562 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_1562 v0 v1 v2 v3 v4 v5 v6 ~v7
                                          ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_checkElab'45'fallback'45'RDestruct_1562 v0 v1 v2 v3 v4 v5 v6
du_checkElab'45'fallback'45'RDestruct_1562 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_1562 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6232
              (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
                  -> let v15
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v10) (coe v1) in
                     coe
                       (case coe v15 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                            -> if coe v16
                                 then case coe v17 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v10
                                                  v18 v12)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v17)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnaryOp
d_checkElab'45'fallback'45'RUnaryOp_1792 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_1792 v0 ~v1 v2 v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_1792 v0 v2 v3
du_checkElab'45'fallback'45'RUnaryOp_1792 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_1792 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_120
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                          (coe MAlonzo.Code.Once.Type.C_Int_134)
                          (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_int_186
                             (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_130
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                          (coe MAlonzo.Code.Once.Type.C_Float_136)
                          (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_float_194
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
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_134
           -> let v5
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_2758
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                           (coe v1)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                            -> let v13
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                         (coe v2) (coe v2) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                      -> if coe v14
                                           then case coe v15 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                            v2 v16 v10)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v12) erased))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v15)
                                                  (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnaryOp-sub
d_checkElab'45'fallback'45'RUnaryOp'45'sub_2016 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp'45'sub_2016 v0 v1 ~v2 v3 v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9 v10
  = du_checkElab'45'fallback'45'RUnaryOp'45'sub_2016 v0 v1 v3 v4 v10
du_checkElab'45'fallback'45'RUnaryOp'45'sub_2016 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp'45'sub_2016 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
              (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_120
           -> case coe v2 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
                  -> coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                             (coe MAlonzo.Code.Once.Type.C_Int_134)
                             (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'int_56)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_int_186
                                (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v7))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_130
           -> case coe v2 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v10 v11 v12 v13
                  -> coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                             (coe MAlonzo.Code.Once.Type.C_Float_136)
                             (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'float_58)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_float_194
                                (coe
                                   MAlonzo.Code.Once.Float.Decimal.C__'47'10'94'__16
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'45'__260
                                      (coe
                                         addInt
                                         (coe
                                            mulInt (coe v10)
                                            (coe
                                               MAlonzo.Code.Data.Nat.Base.d__'94'__276
                                               (coe (10 :: Integer)) (coe v12)))
                                         (coe v11)))
                                   (coe v12))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_134
           -> let v7
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_2758
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                           (coe v2)) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
                            -> let v15
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                         (coe v3) (coe v1) in
                               coe
                                 (case coe v15 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                      -> if coe v16
                                           then case coe v17 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                            v3 v18 v12)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v14) erased))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v17)
                                                  (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-infer
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 v0 v1 v2 v3
                                                       ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328
      v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2634 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_2402 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_2402 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
         (coe MAlonzo.Code.Once.Type.C_Unit_120)
         (coe MAlonzo.Code.Once.Type.Sub.C_sub'45'unit_54)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-lookup-aux-fail
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_2424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_2424 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-bridge
d_inferElabV'45'RVar'45'poly'45'bridge_2434 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'bridge_2434 = erased
-- Once.TypeCheck.ElaborateProofs._.helper
d_helper_2456 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_2456 = erased
-- Once.TypeCheck.ElaborateProofs._.bridge-eq
d_bridge'45'eq_2458 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'eq_2458 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2472 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2500 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2500 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2524 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2524
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2548
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2582 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2582 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-fail-bridge
d_inferElabV'45'RVar'45'fail'45'bridge_2610 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'fail'45'bridge_2610 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_2634 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_2634 v0 ~v1 v2
  = du_checkElab'45'fallback'45'RVar'45'id_2634 v0 v2
du_checkElab'45'fallback'45'RVar'45'id_2634 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_2634 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                             (coe MAlonzo.Code.Once.IR.C_id_20))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.just≢nothing-Maybe
d_just'8802'nothing'45'Maybe_2658 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_2658 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_2674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_2674 v0 ~v1 v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'fst_2674 v0 v2
du_checkElab'45'fallback'45'RVar'45'fst_2674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_2674 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                             (coe MAlonzo.Code.Once.IR.C_fst_42))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_2714 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_2714 v0 ~v1 ~v2 v3
  = du_checkElab'45'fallback'45'RVar'45'snd_2714 v0 v3
du_checkElab'45'fallback'45'RVar'45'snd_2714 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_2714 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                             (coe MAlonzo.Code.Once.IR.C_snd_48))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_2752 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_2752 v0 ~v1 ~v2
  = du_checkElab'45'fallback'45'RVar'45'terminal_2752 v0
du_checkElab'45'fallback'45'RVar'45'terminal_2752 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_2752 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
         (coe MAlonzo.Code.Once.IR.C_terminal_72))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminalV
d_checkElab'45'fallback'45'RVar'45'terminalV_2772 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_2772 v0 ~v1 ~v2
  = du_checkElab'45'fallback'45'RVar'45'terminalV_2772 v0
du_checkElab'45'fallback'45'RVar'45'terminalV_2772 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_2772 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
         (coe MAlonzo.Code.Once.IR.C_terminal_72))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe
                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448)
               erased)))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_2790 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_2790 v0 ~v1 ~v2
  = du_checkElab'45'fallback'45'RVar'45'initial_2790 v0
du_checkElab'45'fallback'45'RVar'45'initial_2790 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_2790 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
         (coe MAlonzo.Code.Once.IR.C_initial_76))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_2810 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_2810 v0 ~v1 v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'inl_2810 v0 v2
du_checkElab'45'fallback'45'RVar'45'inl_2810 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_2810 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                             (coe MAlonzo.Code.Once.IR.C_inl_54))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_2850 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_2850 v0 ~v1 ~v2 v3
  = du_checkElab'45'fallback'45'RVar'45'inr_2850 v0 v3
du_checkElab'45'fallback'45'RVar'45'inr_2850 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_2850 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418
                             (coe MAlonzo.Code.Once.IR.C_inr_60))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                                erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkInGo-J
d_checkInGo'45'J_2886 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2886 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_2918 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_2918 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkInGo'45'just'45'success_2918 v0 v1 v2 v3
du_checkInGo'45'just'45'success_2918 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_2918 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2)
                 (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v7 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v7
                          (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                             (coe v2) (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v2)))
                          (coe
                             MAlonzo.Code.Once.IR.C_In_94
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v2) (coe v3)))
                          v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v9))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-In
d_checkElab'45'fallback'45'RApp'45'In_2970 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_2970 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'In_2970 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'In_2970 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_2970 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_2918 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_2918 (coe v0) (coe v1) (coe v2)
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
                        du_checkInGo'45'just'45'success_2918 (coe v0) (coe v1) (coe v2)
                        (coe v3)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.via
d_via_3026 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_via_3026 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14
  = du_via_3026 v5 v14
du_via_3026 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_via_3026 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe seq (coe v2) (coe v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.apply-pure
d_apply'45'pure_3058 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'pure_3058 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_apply'45'pure_3058 v2 v3 v4 v5 v6 v7
du_apply'45'pure_3058 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'pure_3058 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v0) (coe v0) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v2
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                                   (coe v1))
                                (coe v0))
                             (coe MAlonzo.Code.Once.IR.C_apply_90) v3)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v4))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)))
                else coe
                       seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.apply-eff
d_apply'45'eff_3096 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'eff_3096 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_apply'45'eff_3096 v2 v3 v4 v5 v6 v7
du_apply'45'eff_3096 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'eff_3096 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192 (coe v0) (coe v0) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v2
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                      (coe MAlonzo.Code.Once.Type.C_eff_36))
                                   (coe v1))
                                (coe v0))
                             (coe
                                MAlonzo.Code.Once.IR.C_curry_84
                                (coe
                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                   (coe
                                      MAlonzo.Code.Once.IRTy.C__'42'__20
                                      (coe
                                         MAlonzo.Code.Once.IRTy.C__'8667'__24
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0))
                                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
                                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v0)))
                                   (coe MAlonzo.Code.Once.IR.C_apply_90)
                                   (coe MAlonzo.Code.Once.IR.C_fst_42)))
                             v3)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v4))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)))
                else coe
                       seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_3134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_3134 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply_3134
      v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'apply_3134 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_3134 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = let v9
          = coe
              du_via_3026
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2))
              (\ v9 ->
                 coe
                   du_apply'45'pure_3058 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8)) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v13)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 (coe v0)
                          (coe v1) (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-effclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210
      v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3210 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_via_3026
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2))
              (\ v9 ->
                 coe
                   du_apply'45'eff_3096 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8)) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v13)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2328 (coe v0)
                          (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                             (coe MAlonzo.Code.Once.Type.C_Unit_120)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_eff_36))
                             (coe v4)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.resolveExprWF
d_resolveExprWF_3272 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExprWF_3272 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_resolveExprWF_3272 v3 v4 v6 v7 v8 v9
du_resolveExprWF_3272 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExprWF_3272 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_16 v8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v9 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v9
                    (coe
                       du_resolveExprWF_3272 (coe v18) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v8 v9 v10 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_50 v8 v9 v10 v12
             (coe
                du_resolveExprWF_3272
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v0))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v13))
             (coe
                du_resolveExprWF_3272 (coe v10) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v8 v9 v10 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v8 v9 v10
                    (coe
                       du_resolveExprWF_3272
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v16))
                       (coe v1) (coe v2) (coe v3) (coe v4) (coe v12))
                    (coe
                       du_resolveExprWF_3272 (coe v10) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v8 v9 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v8 v9
                    (coe
                       du_resolveExprWF_3272 (coe v14) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v12))
                    (coe
                       du_resolveExprWF_3272 (coe v15) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v10
             (coe
                du_resolveExprWF_3272
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v0) (coe v10))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v9 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v9
             (coe
                du_resolveExprWF_3272
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v9) (coe v0))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_114 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_114
                    (coe
                       du_resolveExprWF_3272 (coe v12) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_126 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_126
                    (coe
                       du_resolveExprWF_3272 (coe v13) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v8 v9 v10 v11 v12 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v8 v9 v10 v11 v12 v13
             v14
             (coe
                du_resolveExprWF_3272
                (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v13) (coe v14))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v16))
             (coe
                du_resolveExprWF_3272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v17))
             (coe
                du_resolveExprWF_3272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v18))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_154
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_154
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_164 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_164
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Void_122)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v8 v9 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v8 v9 v10 v11
             (coe
                du_resolveExprWF_3272 (coe v11) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v13))
             (coe
                du_resolveExprWF_3272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_int_186 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_186 v8
      MAlonzo.Code.Once.Surface.Syntax.C_float_194 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_194 v8
      MAlonzo.Code.Once.Surface.Syntax.C_add_204 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_204 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Float_136)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_272 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_272
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_div_282 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_282 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_300
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_le_320 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_320 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v8 v9
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3272 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v9 v11
             (coe
                du_resolveExprWF_3272 (coe v9) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v9 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v9 v10
      MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v9
      MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v8
        -> coe
             du_resolvePolyCase_3286 (coe v2) (coe v3) (coe v4) (coe v8)
             (coe v0)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_144
                (coe v1) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_closed_406
             (coe
                du_resolveExprWF_3272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v11
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v9 v11
             (coe
                du_resolveExprWF_3272 (coe v9) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v8 v9 v11 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v8 v9 v11
                           (coe
                              du_resolveExprWF_3272
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                 (coe v18))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                           (coe
                              du_resolveExprWF_3272
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                 (coe v11))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v8 v9 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v19 v20
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v8 v9
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v19)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                        (coe v18))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                        (coe v18))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v8 v9 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v8 v9
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                        (coe v21))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                        (coe v22))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_502 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_curry''_502
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__124 (coe v15) (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                        (coe v20))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v12
                                  (coe
                                     du_resolveExprWF_3272
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17)
                                           (coe v16))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                        (coe v16))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_530 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ana_530 v12
                           (coe
                              du_resolveExprWF_3272
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17)
                                    (coe v14)))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolvePolyCase
d_resolvePolyCase_3286 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvePolyCase_3286 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_resolvePolyCase_3286 v4 v5 v6 v7 v8 v9
du_resolvePolyCase_3286 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvePolyCase_3286 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           du_applySplice_3306 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v9) (coe v10)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                 (coe v0 v3) (coe v10))
                              (coe v9) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.applySplice
d_applySplice_3306 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_applySplice_3306 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12
                   v13
  = du_applySplice_3306 v4 v5 v6 v7 v8 v10 v11 v13
du_applySplice_3306 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_applySplice_3306 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v10 v11 v12 v13
               -> coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_406
                       (coe
                          du_resolveExprWF_3272 (coe v4) (coe v6) (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                (coe (0 :: Integer)) (coe v0 v3) (coe v6))
                             (coe v5) (coe v4)
                             (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v9))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v10
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_3954 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExpr_3954 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_resolveExpr_3954 v3 v4 v5 v6 v7 v8
du_resolveExpr_3954 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExpr_3954 v0 v1 v2 v3 v4 v5
  = coe
      du_resolveExprWF_3272 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_3980 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_3980 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_4010 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_4010 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_4038 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_4038 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_4064 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_4064 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_4090 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_4090 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_4112 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_4112 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_4134 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_4134 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_4156 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_4156 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_4178 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_4178 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_4214 ::
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
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_4214 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_4228 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_4228 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_4248 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_4248 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_4276 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_4276 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_4292 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_4292 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_4314 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'add_4314 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_4336 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sub_4336 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_4358 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mul_4358 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_4380 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'div_4380 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_4402 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mod''_4402 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_4420 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_4420 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_4442 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lt_4442 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_4464 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'le_4464 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_4486 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'gt_4486 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_4508 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ge_4508 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_4530 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'eq_4530 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_4552 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ne_4552 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-coerce
d_resolveExpr'45'coerce_4576 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'coerce_4576 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_4596 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp'45'extern_4596 = erased
-- Once.TypeCheck.ElaborateProofs.poly-check-eq
d_poly'45'check'45'eq_4626 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'check'45'eq_4626 = erased
-- Once.TypeCheck.ElaborateProofs.poly-ground-eq
d_poly'45'ground'45'eq_4660 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'ground'45'eq_4660 = erased
-- Once.TypeCheck.ElaborateProofs.poly-inst-yes
d_poly'45'inst'45'yes_4700 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'inst'45'yes_4700 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_4786 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_4786 v0 v1 ~v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RVar'45'poly_4786 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly_4786 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_4786 v0 v1
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
           -> coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
                         erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly-infer
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850 v0 v1 ~v2 ~v3
                                                      ~v4 ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4850 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_398 (coe v0))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_4890 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_4890 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'id_4890 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'id_4890 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_4890 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_id_20) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (let v14
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                     (coe v3) (coe v1) in
                           coe
                             (case coe v14 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                  -> if coe v15
                                       then case coe v16 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                        v3 v17 v12)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v13)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v11) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v16)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-fst
d_checkElab'45'fallback'45'RApp'45'fst_4978 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_4978 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'fst_4978 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'fst_4978 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_4978 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2372 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-snd
d_checkElab'45'fallback'45'RApp'45'snd_5066 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_5066 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'snd_5066 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'snd_5066 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_5066 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2448 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkViewBridge
d_checkViewBridge_5144 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_798 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_5144 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_5170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_5170 v0 v1 v2 v3 v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'generic_5170 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'generic_5170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_5170 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6280
              (coe v0) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_844
                 (coe v2)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v4) (coe v1) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v4
                                                  v16 v10)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v15)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferOutGo-J
d_inferOutGo'45'J_5272 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferOutGo'45'J_5272 = erased
-- Once.TypeCheck.ElaborateProofs.cata-go-canonical
d_cata'45'go'45'canonical_5306 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_5306 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-J
d_checkCataGo'45'J_5322 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'J_5322 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_5346 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_5346 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_5380 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'just'45'success_5380 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-J
d_checkAnaGo'45'J_5436 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'J_5436 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGoV-J
d_checkAnaGoV'45'J_5466 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGoV'45'J_5466 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-just-success
d_checkAnaGo'45'just'45'success_5504 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'just'45'success_5504 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_5572 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_5572 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_5654 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_5654 v0 v1 v2 v3 ~v4
                                                 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'terminal_5654 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'terminal_5654 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_5654 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_terminal_72) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (let v14
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                                     (coe v3) (coe v1) in
                           coe
                             (case coe v14 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                  -> if coe v15
                                       then case coe v16 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_372
                                                        v3 v17 v12)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v13)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v11) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v16)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-Out
d_checkElab'45'fallback'45'RApp'45'Out_5742 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'Out_5742 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'Out_5742 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'Out_5742 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'Out_5742 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferOutOn_2296 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v3) (coe v1) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                            -> if coe v13
                                 then case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v3
                                                  v15 v9)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v11) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v14)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RBinOp
d_checkElab'45'fallback'45'RBinOp_5834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_5834 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RBinOp_5834 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RBinOp_5834 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_5834 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_2936
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v3))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
                 (coe v4)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__392
                               (coe v8) (coe v1) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v8
                                                  v16 v10)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v11)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v12) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v15)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExprTyped
d_compileExprTyped_6016 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_6016 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6180
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_406) (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_996
                   (0 :: Integer) (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                   v3 v1 v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExpr
d_compileExpr_6040 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_6040 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_406)
                 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_996
                      (0 :: Integer) (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                      v3 v2 v4))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferElabProj
d_inferElabProj_6062 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_74
d_inferElabProj_6062 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6164 (coe v0)
         (coe v1))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_6078 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98
d_checkElabProj_6078 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172 (coe v0)
         (coe v1) (coe v2))
