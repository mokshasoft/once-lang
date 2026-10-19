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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RInt
d_checkElab'45'fallback'45'RInt_16 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_16 ~v0 v1
  = du_checkElab'45'fallback'45'RInt_16 v1
du_checkElab'45'fallback'45'RInt_16 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RInt_16 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RFloat
d_checkElab'45'fallback'45'RFloat_52 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_52 ~v0 v1 v2 v3 ~v4
  = du_checkElab'45'fallback'45'RFloat_52 v1 v2 v3
du_checkElab'45'fallback'45'RFloat_52 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_52 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
         (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_198
            (coe
               MAlonzo.Code.Once.Spec.Float.Decimal.C__'47'10'94'__18
               (coe
                  addInt
                  (coe
                     mulInt (coe v0)
                     (coe
                        MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                        (coe v2)))
                  (coe v1))
               (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_98 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_98 ~v0
  = du_checkElab'45'fallback'45'RUnit_98
du_checkElab'45'fallback'45'RUnit_98 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnit_98
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RResolved
d_checkElab'45'fallback'45'RResolved_134 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RResolved_134 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RResolved_134 v0 v1 v2 v3
du_checkElab'45'fallback'45'RResolved_134 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_134 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670
              (coe v2) in
    coe
      (let v5
             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'RResolved'45'dispatch_5736
                 (coe v0) (coe v2)
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670 (coe v2)) in
       coe
         (coe
            seq (coe v4)
            (case coe v5 of
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                 -> case coe v6 of
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                        -> let v13
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
d_checkElab'45'fallback'45'RAnnot_984 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_984 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                      ~v8 ~v9
  = du_checkElab'45'fallback'45'RAnnot_984 v0 v1 v2 v3
du_checkElab'45'fallback'45'RAnnot_984 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_984 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2846
              (coe v3)
              (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v3))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6214 (coe v0)
                 (coe v2) (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
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
d_checkElab'45'fallback'45'RLet_1162 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_1162 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8
                                     ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RLet_1162 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RLet_1162 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_1162 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6260
              (coe v0) (coe v2) (coe v4)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v8
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
d_checkElab'45'fallback'45'RDestruct_1372 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_1372 v0 v1 v2 v3 v4 v5 v6 ~v7
                                          ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_checkElab'45'fallback'45'RDestruct_1372 v0 v1 v2 v3 v4 v5 v6
du_checkElab'45'fallback'45'RDestruct_1372 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_1372 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6274
              (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
                  -> let v15
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v10
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
d_checkElab'45'fallback'45'RUnaryOp_1602 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_UnaryOp_30 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_1602 v0 ~v1 v2 v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_1602 v0 v2 v3
du_checkElab'45'fallback'45'RUnaryOp_1602 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_1602 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
              (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_120
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_int_190
                             (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_130
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_float_198
                             (coe
                                MAlonzo.Code.Once.Spec.Float.Decimal.C__'47'10'94'__18
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
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_134
           -> let v5
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_2886
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                           (coe v1)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                            -> let v13
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
d_checkElab'45'fallback'45'RUnaryOp'45'sub_1826 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_UnaryOp_30 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp'45'sub_1826 v0 v1 ~v2 v3 v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9 v10
  = du_checkElab'45'fallback'45'RUnaryOp'45'sub_1826 v0 v1 v3 v4 v10
du_checkElab'45'fallback'45'RUnaryOp'45'sub_1826 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp'45'sub_1826 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
              (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_120
           -> case coe v2 of
                MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v7
                  -> coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'int_34)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_int_190
                                (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v7))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_130
           -> case coe v2 of
                MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v10 v11 v12 v13
                  -> coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                             (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'float_36)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_float_198
                                (coe
                                   MAlonzo.Code.Once.Spec.Float.Decimal.C__'47'10'94'__18
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
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_134
           -> let v7
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_2886
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                           (coe v2)) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
                            -> let v15
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 v0 v1 v2 v3
                                                       ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138
      v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2762 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
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
d_checkElab'45'fallback'45'RVar'45'unit_2212 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_2212 ~v0
  = du_checkElab'45'fallback'45'RVar'45'unit_2212
du_checkElab'45'fallback'45'RVar'45'unit_2212 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'unit_2212
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-lookup-aux-fail
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_2234 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'lookup'45'aux'45'fail_2234 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-bridge
d_inferElabV'45'RVar'45'poly'45'bridge_2244 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'bridge_2244 = erased
-- Once.TypeCheck.ElaborateProofs._.helper
d_helper_2266 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_2266 = erased
-- Once.TypeCheck.ElaborateProofs._.bridge-eq
d_bridge'45'eq_2268 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'eq_2268 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2282 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2282 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2310 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2310 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2334 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2334
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2358 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2358
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2392 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2392 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-fail-bridge
d_inferElabV'45'RVar'45'fail'45'bridge_2420 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'fail'45'bridge_2420 = erased
-- Once.TypeCheck.ElaborateProofs.withUnit-elim
d_withUnit'45'elim_2446 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  (MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> AgdaAny) ->
  AgdaAny
d_withUnit'45'elim_2446 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_withUnit'45'elim_2446 v3 v6
du_withUnit'45'elim_2446 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  (MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 -> AgdaAny) ->
  AgdaAny
du_withUnit'45'elim_2446 v0 v1 = coe seq (coe v0) (coe v1 v0)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_2486 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_2486 ~v0 ~v1 v2 v3
  = du_checkElab'45'fallback'45'RVar'45'id_2486 v2 v3
du_checkElab'45'fallback'45'RVar'45'id_2486 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_2486 v0 v1
  = let v2
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          du_withUnit'45'elim_2446 (coe v1)
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe MAlonzo.Code.Once.IR.C_id_20))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.just≢nothing-Maybe
d_just'8802'nothing'45'Maybe_2526 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_2526 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_2544 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_2544 ~v0 ~v1 v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'fst_2544 v2 v4
du_checkElab'45'fallback'45'RVar'45'fst_2544 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_2544 v0 v1
  = let v2
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          du_withUnit'45'elim_2446 (coe v1)
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_2602 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_2602 ~v0 ~v1 ~v2 v3 v4
  = du_checkElab'45'fallback'45'RVar'45'snd_2602 v3 v4
du_checkElab'45'fallback'45'RVar'45'snd_2602 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_2602 v0 v1
  = let v2
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          du_withUnit'45'elim_2446 (coe v1)
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe MAlonzo.Code.Once.IR.C_snd_48))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_2658 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_2658 ~v0 ~v1 ~v2 v3
  = du_checkElab'45'fallback'45'RVar'45'terminal_2658 v3
du_checkElab'45'fallback'45'RVar'45'terminal_2658 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_2658 v0
  = coe
      du_withUnit'45'elim_2446 (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                 (coe MAlonzo.Code.Once.IR.C_terminal_72))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminalV
d_checkElab'45'fallback'45'RVar'45'terminalV_2692 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_2692 ~v0 ~v1 ~v2 v3
  = du_checkElab'45'fallback'45'RVar'45'terminalV_2692 v3
du_checkElab'45'fallback'45'RVar'45'terminalV_2692 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_2692 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
            (coe MAlonzo.Code.Once.IR.C_terminal_72))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_462
                     v0)
                  erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_2720 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_2720 ~v0 ~v1 ~v2 v3
  = du_checkElab'45'fallback'45'RVar'45'initial_2720 v3
du_checkElab'45'fallback'45'RVar'45'initial_2720 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_2720 v0
  = coe
      du_withUnit'45'elim_2446 (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                 (coe MAlonzo.Code.Once.IR.C_initial_76))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_2754 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_2754 ~v0 ~v1 v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'inl_2754 v2 v4
du_checkElab'45'fallback'45'RVar'45'inl_2754 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_2754 v0 v1
  = let v2
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          du_withUnit'45'elim_2446 (coe v1)
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe MAlonzo.Code.Once.IR.C_inl_54))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_2812 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_2812 ~v0 ~v1 ~v2 v3 v4
  = du_checkElab'45'fallback'45'RVar'45'inr_2812 v3 v4
du_checkElab'45'fallback'45'RVar'45'inr_2812 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_2812 v0 v1
  = let v2
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          du_withUnit'45'elim_2446 (coe v1)
                          (coe
                             (\ v5 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe MAlonzo.Code.Once.IR.C_inr_60))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkInGo-J
d_checkInGo'45'J_2864 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2864 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_2896 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_2896 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9
  = du_checkInGo'45'just'45'success_2896 v0 v1 v2 v3
du_checkInGo'45'just'45'success_2896 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_2896 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6222
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v2)
                 (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v2))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v7 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v7
                          (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                             (coe v2) (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v2)))
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
d_checkElab'45'fallback'45'RApp'45'In_2948 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_2948 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'In_2948 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'In_2948 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_2948 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_2896 (coe v0) (coe v1) (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_2896 (coe v0) (coe v1) (coe v2)
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
                        du_checkInGo'45'just'45'success_2896 (coe v0) (coe v1) (coe v2)
                        (coe v3)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.via
d_via_3004 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_via_3004 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 v14
  = du_via_3004 v5 v14
du_via_3004 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_via_3004 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe seq (coe v2) (coe v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.apply-pure
d_apply'45'pure_3036 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'pure_3036 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_apply'45'pure_3036 v2 v3 v4 v5 v6 v7
du_apply'45'pure_3036 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'pure_3036 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v2
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
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
d_apply'45'eff_3074 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'eff_3074 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_apply'45'eff_3074 v2 v3 v4 v5 v6 v7
du_apply'45'eff_3074 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'eff_3074 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v2
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
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
-- Once.TypeCheck.ElaborateProofs.apply-act
d_apply'45'act_3112 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'act_3112 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_apply'45'act_3112 v2 v3 v4 v5 v6 v7
du_apply'45'act_3112 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'act_3112 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216
              (coe v0) (coe v0) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v2
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
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
d_checkElab'45'fallback'45'RApp'45'apply_3150 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_3150 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply_3150
      v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'apply_3150 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_3150 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8
  = let v9
          = coe
              du_via_3004
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2))
              (\ v9 ->
                 coe
                   du_apply'45'pure_3036 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8)) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v13)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 (coe v0)
                          (coe v1) (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-effclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226
      v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3226 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_via_3004
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2))
              (\ v9 ->
                 coe
                   du_apply'45'eff_3074 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8)) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v13)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 (coe v0)
                          (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
                             (coe v4)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-actclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302
      v0 v1 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3302 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8
  = let v9
          = coe
              du_via_3004
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2))
              (\ v9 ->
                 coe
                   du_apply'45'act_3112 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8)) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v13)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2138 (coe v0)
                          (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                             (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                             (coe v4)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.resolveExprWF
d_resolveExprWF_3364 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExprWF_3364 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_resolveExprWF_3364 v3 v4 v6 v7 v8 v9
du_resolveExprWF_3364 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExprWF_3364 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_16 v8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v9 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v9
                    (coe
                       du_resolveExprWF_3364 (coe v18) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v8 v9 v10 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_50 v8 v9 v10 v12
             (coe
                du_resolveExprWF_3364
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v12)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                   (coe v0))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v13))
             (coe
                du_resolveExprWF_3364 (coe v10) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v8 v9 v10 v13 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v8 v9 v10 v13
                           (coe
                              du_resolveExprWF_3364
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v20))
                                 (coe v18))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                           (coe
                              du_resolveExprWF_3364 (coe v10) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v8 v9 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v8 v9
                    (coe
                       du_resolveExprWF_3364 (coe v14) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v12))
                    (coe
                       du_resolveExprWF_3364 (coe v15) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v10
             (coe
                du_resolveExprWF_3364
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v0) (coe v10))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v9 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v9
             (coe
                du_resolveExprWF_3364
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v9) (coe v0))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_118
                    (coe
                       du_resolveExprWF_3364 (coe v12) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_130
                    (coe
                       du_resolveExprWF_3364 (coe v13) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v8 v9 v10 v11 v12 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v8 v9 v10 v11 v12 v13
             v14
             (coe
                du_resolveExprWF_3364
                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v13) (coe v14))
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v16))
             (coe
                du_resolveExprWF_3364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v17))
             (coe
                du_resolveExprWF_3364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v18))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_168
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v8 v9 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v8 v9 v10 v11
             (coe
                du_resolveExprWF_3364 (coe v11) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v13))
             (coe
                du_resolveExprWF_3364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v8
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_198 v8
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_208 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_286 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_304
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_324 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v8 v9
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v10))
             (coe
                du_resolveExprWF_3364 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v9 v11
             (coe
                du_resolveExprWF_3364 (coe v9) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v9 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v9 v10
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v9
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v8
        -> coe
             du_resolvePolyCase_3378 (coe v2) (coe v3) (coe v4) (coe v8)
             (coe v0)
             (coe
                MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupPolyPrefix_68 (coe v1)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_closed_410
             (coe
                du_resolveExprWF_3364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v11
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v9 v11
             (coe
                du_resolveExprWF_3364 (coe v9) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v8 v9 v11 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v8 v9 v11
                           (coe
                              du_resolveExprWF_3364
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v20))
                                 (coe v18))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                           (coe
                              du_resolveExprWF_3364
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v20))
                                 (coe v11))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v8 v9 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v19 v20
                      -> case coe v17 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v8 v9
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v19)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v22))
                                        (coe v18))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v22))
                                        (coe v18))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v8 v9 v14 v15
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v8 v9
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v20))
                                        (coe v21))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v20))
                                        (coe v22))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_curry''_506
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v15)
                                           (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v22))
                                        (coe v20))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v8 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v8 v12
                                  (coe
                                     du_resolveExprWF_3364
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v17) (coe v16))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v19))
                                        (coe v16))
                                     (coe v1) (coe v2) (coe v3) (coe v4) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v8 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v8 v13
                           (coe
                              du_resolveExprWF_3364
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v19)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v18)
                                    (coe v15)))
                              (coe v1) (coe v2) (coe v3) (coe v4) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v8 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v8
                    (coe
                       du_resolveExprWF_3364
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                          (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v14) (coe v12)))
                       (coe v1) (coe v2) (coe v3) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolvePolyCase
d_resolvePolyCase_3378 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolvePolyCase_3378 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10
  = du_resolvePolyCase_3378 v4 v5 v6 v7 v8 v9
du_resolvePolyCase_3378 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolvePolyCase_3378 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           du_applySplice_3398 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v9) (coe v10)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6214
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                                 (coe v0 v3) (coe v10))
                              (coe v9) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.applySplice
d_applySplice_3398 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_applySplice_3398 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 ~v9 v10 v11 ~v12
                   v13
  = du_applySplice_3398 v4 v5 v6 v7 v8 v10 v11 v13
du_applySplice_3398 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_applySplice_3398 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v10 v11 v12 v13
               -> coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_410
                       (coe
                          du_resolveExprWF_3364 (coe v4) (coe v6) (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0 v3))
                                (coe v6)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0 v3)))
                             (coe v5) (coe v4)
                             (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v9))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v10
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_4060 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_resolveExpr_4060 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_resolveExpr_4060 v3 v4 v5 v6 v7 v8
du_resolveExpr_4060 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_resolveExpr_4060 v0 v1 v2 v3 v4 v5
  = coe
      du_resolveExprWF_3364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_4086 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_4086 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_4116 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_4116 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_4144 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_4144 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_4170 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_4170 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_4200 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_56 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_4200 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_4222 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_4222 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_4244 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_4244 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_4266 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_4266 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_4288 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_4288 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_4324 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_4324 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_4338 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_4338 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_4358 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_4358 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_4386 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_4386 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_4402 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_4402 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_4424 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'add_4424 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_4446 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sub_4446 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_4468 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mul_4468 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_4490 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'div_4490 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_4512 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mod''_4512 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_4530 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_4530 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_4552 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lt_4552 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_4574 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'le_4574 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_4596 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'gt_4596 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_4618 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ge_4618 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_4640 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'eq_4640 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_4662 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ne_4662 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-coerce
d_resolveExpr'45'coerce_4686 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'coerce_4686 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_4706 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp'45'extern_4706 = erased
-- Once.TypeCheck.ElaborateProofs.poly-check-eq
d_poly'45'check'45'eq_4732 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'check'45'eq_4732 = erased
-- Once.TypeCheck.ElaborateProofs.poly-ground-eq
d_poly'45'ground'45'eq_4766 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'ground'45'eq_4766 = erased
-- Once.TypeCheck.ElaborateProofs.poly-inst-yes
d_poly'45'inst'45'yes_4806 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'inst'45'yes_4806 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_4892 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_4892 v0 v1 ~v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RVar'45'poly_4892 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly_4892 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_4892 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_4718
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
           -> coe
                seq (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                         erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly-infer
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956 ~v0 v1 ~v2
                                                      ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956 v1
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_4956 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_4996 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_4996 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'id_4996 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'id_4996 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_4996 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_id_20) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (let v14
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
d_checkElab'45'fallback'45'RApp'45'fst_5084 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_5084 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'fst_5084 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'fst_5084 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_5084 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2436 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
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
d_checkElab'45'fallback'45'RApp'45'snd_5172 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_5172 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'snd_5172 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'snd_5172 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_5172 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2512 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
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
d_checkViewBridge_5250 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_AppHeadView_298 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_5250 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_5276 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_5276 v0 v1 v2 v3 v4 ~v5
                                                ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'generic_5276 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'generic_5276 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_5276 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6322
              (coe v0) (coe v2) (coe v3)
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_classifyAppHeadView_344
                 (coe v2)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v4
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
d_inferOutGo'45'J_5378 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferOutGo'45'J_5378 = erased
-- Once.TypeCheck.ElaborateProofs.cata-go-canonical
d_cata'45'go'45'canonical_5412 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_5412 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-J
d_checkCataGo'45'J_5428 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'J_5428 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_5452 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_5452 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_5488 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'just'45'success_5488 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-J
d_checkAnaGo'45'J_5622 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'J_5622 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGoV-J
d_checkAnaGoV'45'J_5656 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGoV'45'J_5656 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-just-success
d_checkAnaGo'45'just'45'success_5708 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'just'45'success_5708 = erased
-- Once.TypeCheck.ElaborateProofs.checkLoopV-J
d_checkLoopV'45'J_5856 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkLoopV'45'J_5856 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_5890 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_5890 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_5972 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_5972 v0 v1 v2 v3 ~v4
                                                 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'terminal_5972 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'terminal_5972 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_5972 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8 v7
                               (coe MAlonzo.Code.Once.IR.C_terminal_72) v9 in
                     coe
                       (let v13 = addInt (coe (1 :: Integer)) (coe v10) in
                        coe
                          (let v14
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
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
d_checkElab'45'fallback'45'RApp'45'Out_6060 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'Out_6060 v0 v1 v2 v3 ~v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'Out_6060 v0 v1 v2 v3
du_checkElab'45'fallback'45'RApp'45'Out_6060 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'Out_6060 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferOutOn_2360 (coe v0)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v2)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v3
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
d_checkElab'45'fallback'45'RBinOp_6152 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_6152 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RBinOp_6152 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RBinOp_6152 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_6152 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_3064
              (coe v2)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v3))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
                 (coe v4)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160
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
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v8
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
d_compileExprTyped_6334 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_6334 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6222
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_330) (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_1068
                   (0 :: Integer) (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) v3
                   v1 v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExpr
d_compileExpr_6358 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_6358 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_330)
                 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_1068
                      (0 :: Integer) (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) v3
                      v2 v4))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferElabProj
d_inferElabProj_6380 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_74
d_inferElabProj_6380 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6206 (coe v0)
         (coe v1))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_6396 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98
d_checkElabProj_6396 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6214 (coe v0)
         (coe v1) (coe v2))
