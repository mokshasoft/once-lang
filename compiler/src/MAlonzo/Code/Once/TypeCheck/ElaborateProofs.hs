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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Internal.Name
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
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
d_checkElab'45'fallback'45'RInt_18 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_18 ~v0 ~v1 v2
  = du_checkElab'45'fallback'45'RInt_18 v2
du_checkElab'45'fallback'45'RInt_18 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RInt_18 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RFloat
d_checkElab'45'fallback'45'RFloat_62 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_62 ~v0 ~v1 v2 v3 v4 ~v5
  = du_checkElab'45'fallback'45'RFloat_62 v2 v3 v4
du_checkElab'45'fallback'45'RFloat_62 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_62 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_202
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
d_checkElab'45'fallback'45'RUnit_116 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_116 ~v0 ~v1
  = du_checkElab'45'fallback'45'RUnit_116
du_checkElab'45'fallback'45'RUnit_116 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnit_116
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RResolved
d_checkElab'45'fallback'45'RResolved_160 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RResolved_160 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                         ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RResolved_160 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RResolved_160 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_160 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692
              (coe v3) in
    coe
      (let v6
             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'RResolved'45'dispatch_6054
                 (coe v0) (coe v1) (coe v3)
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692 (coe v3)) in
       coe
         (coe
            seq (coe v5)
            (case coe v6 of
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                 -> case coe v7 of
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v9 v10 v11 v12 v13
                        -> let v14
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                     (coe v0) (coe v4) (coe v2) in
                           coe
                             (case coe v14 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                  -> if coe v15
                                       then case coe v16 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                        v4 v17 v11)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v13) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v16)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RAnnot
d_checkElab'45'fallback'45'RAnnot_1012 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_1012 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RAnnot_1012 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RAnnot_1012 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_1012 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_3006
              (coe v0) (coe v4)
              (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_718 (coe v4))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6624 (coe v0)
                 (coe v1) (coe v3)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.d_wk'8320'_30 (coe v0)
                    (coe v4))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                                  (coe (0 :: Integer)) (coe v0) (coe v4)
                                  (\ v13 -> coe MAlonzo.Code.Once.Internal.Type.du_none_26))
                               (coe v2) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                  (MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
                                                     (coe (0 :: Integer)) (coe v0) (coe v4)
                                                     (\ v17 ->
                                                        coe
                                                          MAlonzo.Code.Once.Internal.Type.du_none_26))
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RLet
d_checkElab'45'fallback'45'RLet_1192 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_1192 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                     ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RLet_1192 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RLet_1192 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_1192 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6682
              (coe v0) (coe v1) (coe v3) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v4)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v9 v10 v11 v12 v13
                  -> let v14
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v9) (coe v2) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                            -> if coe v15
                                 then case coe v16 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v9
                                                  v17 v11)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v13) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v16)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RDestruct
d_checkElab'45'fallback'45'RDestruct_1404 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_1404 v0 v1 v2 v3 v4 v5 v6 v7
                                          ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_checkElab'45'fallback'45'RDestruct_1404
      v0 v1 v2 v3 v4 v5 v6 v7
du_checkElab'45'fallback'45'RDestruct_1404 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_1404 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6698
              (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3)) in
    coe
      (case coe v8 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
           -> case coe v9 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v11 v12 v13 v14 v15
                  -> let v16
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v11) (coe v2) in
                     coe
                       (case coe v16 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                            -> if coe v17
                                 then case coe v18 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v11
                                                  v19 v13)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v15) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v18)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnaryOp
d_checkElab'45'fallback'45'RUnaryOp_1636 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_UnaryOp_30 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_1636 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                         ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RUnaryOp_1636 v0 v1 v3 v4
du_checkElab'45'fallback'45'RUnaryOp_1636 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_1636 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_152
              (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_134
           -> case coe v2 of
                MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                          (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_int_194
                             (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v6))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_144
           -> case coe v2 of
                MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v9 v10 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                          (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                          (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_float_202
                             (coe
                                MAlonzo.Code.Once.Spec.Float.Decimal.C__'47'10'94'__18
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                                   (coe
                                      addInt
                                      (coe
                                         mulInt (coe v9)
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'94'__276
                                            (coe (10 :: Integer)) (coe v11)))
                                      (coe v10)))
                                (coe v11))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_148
           -> let v6
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_3048
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                           (coe v1) (coe v2)) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                     -> case coe v7 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v9 v10 v11 v12 v13
                            -> let v14
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                         (coe v0) (coe v3) (coe v3) in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                      -> if coe v15
                                           then case coe v16 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                            v3 v17 v11)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v13) erased))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v16)
                                                  (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RUnaryOp-sub
d_checkElab'45'fallback'45'RUnaryOp'45'sub_1876 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_UnaryOp_30 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp'45'sub_1876 v0 v1 v2 ~v3 v4 v5
                                                ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_checkElab'45'fallback'45'RUnaryOp'45'sub_1876
      v0 v1 v2 v4 v5 v11
du_checkElab'45'fallback'45'RUnaryOp'45'sub_1876 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp'45'sub_1876 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_152
              (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_134
           -> case coe v3 of
                MAlonzo.Code.Once.Internal.Syntax.C_RInt_54 v8
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                             (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_int_194
                                (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v8))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_144
           -> case coe v3 of
                MAlonzo.Code.Once.Internal.Syntax.C_RFloat_56 v11 v12 v13 v14
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                             (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                             (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'float_24)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_float_202
                                (coe
                                   MAlonzo.Code.Once.Spec.Float.Decimal.C__'47'10'94'__18
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'45'__260
                                      (coe
                                         addInt
                                         (coe
                                            mulInt (coe v11)
                                            (coe
                                               MAlonzo.Code.Data.Nat.Base.d__'94'__276
                                               (coe (10 :: Integer)) (coe v13)))
                                         (coe v12)))
                                   (coe v13))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_148
           -> let v8
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RUnaryOp'45'aux_3048
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                           (coe v1) (coe v3)) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                     -> case coe v9 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v11 v12 v13 v14 v15
                            -> let v16
                                     = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                         (coe v0) (coe v4) (coe v2) in
                               coe
                                 (case coe v16 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                      -> if coe v17
                                           then case coe v18 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                            v4 v19 v13)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v15) erased))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           else coe
                                                  seq (coe v18)
                                                  (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-infer
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 v0 v1 v2 v3
                                                       v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208
      v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 v0 v1 v2 v3
                                                        v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2918 (coe v0)
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v4) (coe v2) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v4
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_2284 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_2284 ~v0 ~v1
  = du_checkElab'45'fallback'45'RVar'45'unit_2284
du_checkElab'45'fallback'45'RVar'45'unit_2284 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'unit_2284
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20)
         (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.inferElabV-own-poly-bridge
d_inferElabV'45'own'45'poly'45'bridge_2314 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'own'45'poly'45'bridge_2314 = erased
-- Once.TypeCheck.ElaborateProofs._.own-dispatch
d_own'45'dispatch_2330 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_own'45'dispatch_2330 = erased
-- Once.TypeCheck.ElaborateProofs._._.sig-eq
d_sig'45'eq_2342 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig'45'eq_2342 = erased
-- Once.TypeCheck.ElaborateProofs._._.imp-eq
d_imp'45'eq_2348 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_imp'45'eq_2348 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2364 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2364 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2394 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2394 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2420 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2420
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2446 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2446
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2482 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2482 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-own-fail-bridge
d_inferElabV'45'own'45'fail'45'bridge_2512 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'own'45'fail'45'bridge_2512 = erased
-- Once.TypeCheck.ElaborateProofs.withUnit-elim
d_withUnit'45'elim_2538 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'elim_2538 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_withUnit'45'elim_2538 v3 v6
du_withUnit'45'elim_2538 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'elim_2538 v0 v1 = coe seq (coe v0) (coe v1 v0)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_2580 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_2580 v0 ~v1 ~v2 v3 v4
  = du_checkElab'45'fallback'45'RVar'45'id_2580 v0 v3 v4
du_checkElab'45'fallback'45'RVar'45'id_2580 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_2580 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          du_withUnit'45'elim_2538 (coe v2)
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_id_20))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.just≢nothing-Maybe
d_just'8802'nothing'45'Maybe_2620 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_2620 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_2640 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_2640 v0 ~v1 ~v2 v3 ~v4 v5
  = du_checkElab'45'fallback'45'RVar'45'fst_2640 v0 v3 v5
du_checkElab'45'fallback'45'RVar'45'fst_2640 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_2640 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          du_withUnit'45'elim_2538 (coe v2)
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_2700 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_2700 v0 ~v1 ~v2 ~v3 v4 v5
  = du_checkElab'45'fallback'45'RVar'45'snd_2700 v0 v4 v5
du_checkElab'45'fallback'45'RVar'45'snd_2700 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_2700 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          du_withUnit'45'elim_2538 (coe v2)
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_snd_48))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_2758 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_2758 ~v0 ~v1 ~v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'terminal_2758 v4
du_checkElab'45'fallback'45'RVar'45'terminal_2758 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_2758 v0
  = coe
      du_withUnit'45'elim_2538 (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                 (coe MAlonzo.Code.Once.IR.C_terminal_72))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-terminalV
d_checkElab'45'fallback'45'RVar'45'terminalV_2794 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_2794 ~v0 ~v1 ~v2 ~v3
                                                  v4
  = du_checkElab'45'fallback'45'RVar'45'terminalV_2794 v4
du_checkElab'45'fallback'45'RVar'45'terminalV_2794 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_2794 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
            (coe MAlonzo.Code.Once.IR.C_terminal_72))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Internal.Typing.C_t'45'terminal'45'morph'45'check_484
                     v0)
                  erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_2824 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_2824 ~v0 ~v1 ~v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'initial_2824 v4
du_checkElab'45'fallback'45'RVar'45'initial_2824 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_2824 v0
  = coe
      du_withUnit'45'elim_2538 (coe v0)
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                 (coe MAlonzo.Code.Once.IR.C_initial_76))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                    erased))))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_2860 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_2860 v0 ~v1 ~v2 v3 ~v4 v5
  = du_checkElab'45'fallback'45'RVar'45'inl_2860 v0 v3 v5
du_checkElab'45'fallback'45'RVar'45'inl_2860 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_2860 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          du_withUnit'45'elim_2538 (coe v2)
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_inl_54))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_2920 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_2920 v0 ~v1 ~v2 ~v3 v4 v5
  = du_checkElab'45'fallback'45'RVar'45'inr_2920 v0 v4 v5
du_checkElab'45'fallback'45'RVar'45'inr_2920 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_2920 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          du_withUnit'45'elim_2538 (coe v2)
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426
                                     (coe MAlonzo.Code.Once.IR.C_inr_60))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased)))))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkInGo-J
d_checkInGo'45'J_2974 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2974 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_3008 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_3008 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9 ~v10
  = du_checkInGo'45'just'45'success_3008 v0 v1 v2 v3 v4
du_checkInGo'45'just'45'success_3008 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_3008 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6634
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.Internal.Type.du_'10214'_'10215'T_42 v3
                 (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v8
                          (coe
                             MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
                             (coe MAlonzo.Code.Once.Spec.Type.C_μ_28 (coe v3)))
                          (coe
                             MAlonzo.Code.Once.IR.C_In_94
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v3)
                                (coe v4)))
                          v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v10))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-In
d_checkElab'45'fallback'45'RApp'45'In_3062 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_3062 v0 v1 v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'In_3062 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'In_3062 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_3062 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_3008 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_3008 (coe v0) (coe v1) (coe v2)
                  (coe v3) (coe v4))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        du_checkInGo'45'just'45'success_3008 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.via
d_via_3120 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_via_3120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 v15
  = du_via_3120 v6 v15
du_via_3120 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_via_3120 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe seq (coe v2) (coe v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.apply-pure
d_apply'45'pure_3154 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'pure_3154 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'pure_3154 v0 v3 v4 v5 v6 v7 v8
du_apply'45'pure_3154 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'pure_3154 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v3
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                (coe
                                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                   (coe v2))
                                (coe v1))
                             (coe MAlonzo.Code.Once.IR.C_apply_90) v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v5))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased)))
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.apply-eff
d_apply'45'eff_3194 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'eff_3194 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'eff_3194 v0 v3 v4 v5 v6 v7 v8
du_apply'45'eff_3194 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'eff_3194 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v3
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                (coe
                                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
                                   (coe v2))
                                (coe v1))
                             (coe
                                MAlonzo.Code.Once.IR.C_curry_84
                                (coe
                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                   (coe
                                      MAlonzo.Code.Once.IRTy.C__'42'__20
                                      (coe
                                         MAlonzo.Code.Once.IRTy.C__'8667'__24
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v2)))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                         (coe v1)))
                                   (coe MAlonzo.Code.Once.IR.C_apply_90)
                                   (coe MAlonzo.Code.Once.IR.C_fst_42)))
                             v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v5))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased)))
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.apply-act
d_apply'45'act_3234 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'act_3234 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'act_3234 v0 v3 v4 v5 v6 v7 v8
du_apply'45'act_3234 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'act_3234 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
              (coe v0) (coe v1) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v3
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'42'__22
                                (coe
                                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                         (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                                   (coe v2))
                                (coe v1))
                             (coe
                                MAlonzo.Code.Once.IR.C_curry_84
                                (coe
                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                   (coe
                                      MAlonzo.Code.Once.IRTy.C__'42'__20
                                      (coe
                                         MAlonzo.Code.Once.IRTy.C__'8667'__24
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                            (coe v2)))
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                         (coe v1)))
                                   (coe MAlonzo.Code.Once.IR.C_apply_90)
                                   (coe MAlonzo.Code.Once.IR.C_fst_42)))
                             v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v5))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased)))
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_3274 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_3274 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply_3274
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply_3274 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_3274 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8 v9
  = let v10
          = coe
              du_via_3120
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'pure_3154 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 (coe v0)
                          (coe v1) (coe v2) (coe v3) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-effclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3352 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3352 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3352
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3352 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3352 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = coe
              du_via_3120
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'eff_3194 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 (coe v0)
                          (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
                             (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-actclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3430 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3430 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3430
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3430 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3430 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = coe
              du_via_3120
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'act_3234 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2208 (coe v0)
                          (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                             (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.resolveExprWF
d_resolveExprWF_3494 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolveExprWF_3494 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_resolveExprWF_3494 v0 v4 v5 v7 v8 v9 v10
du_resolveExprWF_3494 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExprWF_3494 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10
                    (coe
                       du_resolveExprWF_3494 (coe v0) (coe v19) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe
                   MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v13)
                      (coe
                         MAlonzo.Code.Once.Spec.Grade.C_fin_42
                         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                   (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v14))
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14
                           (coe
                              du_resolveExprWF_3494 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_3494 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10
                    (coe
                       du_resolveExprWF_3494 (coe v0) (coe v15) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v13))
                    (coe
                       du_resolveExprWF_3494 (coe v0) (coe v16) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v1) (coe v11))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v10) (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_122
                    (coe
                       du_resolveExprWF_3494 (coe v0) (coe v13) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_134
                    (coe
                       du_resolveExprWF_3494 (coe v0) (coe v14) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13
             v14 v15
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v17))
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v18))
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v19))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_162
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_172
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v14))
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
      MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
      MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_308
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3494 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
      MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
      MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v9
        -> coe
             du_resolvePolyCase_3510 (coe v0) (coe v3) (coe v4) (coe v5)
             (coe v9) (coe v1)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_76
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_closed_414 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_closed_414
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12
             (coe
                du_resolveExprWF_3494 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12
                           (coe
                              du_resolveExprWF_3494 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_3494 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v12))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v9 v10 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v20 v21
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_copair''_474 v9 v10
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v19))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v19))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v9 v10 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_492 v9 v10
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v22))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v23))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_510 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_curry''_510
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v16)
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v21))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v9 v11 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_cata_526 v9 v11 v14
                                  (coe
                                     du_resolveExprWF_3494 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Internal.Type.du_'10214'_'10215'T_42
                                           v19 v18)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v18))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v9 v11 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_ana_544 v9 v11 v15
                           (coe
                              du_resolveExprWF_3494 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v21)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.du_'10214'_'10215'T_42 v20 v17))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9
                    (coe
                       du_resolveExprWF_3494 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v13)))
                       (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolvePolyCase
d_resolvePolyCase_3510 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolvePolyCase_3510 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 ~v11
  = du_resolvePolyCase_3510 v0 v5 v6 v7 v8 v9 v10
du_resolvePolyCase_3510 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolvePolyCase_3510 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe
                           du_applySplice_3532 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v10) (coe v11)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6624 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_baseKinds_364 (coe v0))
                                 (coe v1 v4) (coe v11))
                              (coe v10) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.applySplice
d_applySplice_3532 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_applySplice_3532 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 ~v10 v11 v12
                   ~v13 v14
  = du_applySplice_3532 v0 v5 v6 v7 v8 v9 v11 v12 v14
du_applySplice_3532 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_applySplice_3532 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v11 v12 v13 v14
               -> coe
                    seq (coe v11)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_414
                       (coe
                          du_resolveExprWF_3494 (coe v0) (coe v5) (coe v7) (coe v1) (coe v2)
                          (coe v3)
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_22 (coe v0)
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
                                (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1 v4))
                                (coe v7)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1 v4))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_baseKinds_364 (coe v0)))
                             (coe v6) (coe v5)
                             (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36) (coe v10))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v11
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_4196 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_resolveExpr_4196 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_resolveExpr_4196 v0 v4 v5 v6 v7 v8 v9
du_resolveExpr_4196 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExpr_4196 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_resolveExprWF_3494 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_4224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_4224 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_4256 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_4256 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_4286 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_4286 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_4314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_4314 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_4346 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_4346 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_4370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_4370 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_4394 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_4394 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_4418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_4418 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_4442 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_4442 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_4480 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_4480 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_4496 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_4496 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_4518 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_4518 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_4548 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_4548 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_4566 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_4566 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_4590 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'add_4590 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_4614 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sub_4614 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_4638 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mul_4638 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_4662 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'div_4662 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_4686 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mod''_4686 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_4706 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_4706 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_4730 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lt_4730 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_4754 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'le_4754 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_4778 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'gt_4778 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_4802 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ge_4802 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_4826 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'eq_4826 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_4850 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ne_4850 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-coerce
d_resolveExpr'45'coerce_4876 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'coerce_4876 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_4898 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp'45'extern_4898 = erased
-- Once.TypeCheck.ElaborateProofs.poly-check-eq
d_poly'45'check'45'eq_4926 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'check'45'eq_4926 = erased
-- Once.TypeCheck.ElaborateProofs.poly-ground-eq
d_poly'45'ground'45'eq_4962 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'ground'45'eq_4962 = erased
-- Once.TypeCheck.ElaborateProofs.poly-inst-yes
d_poly'45'inst'45'yes_5004 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'inst'45'yes_5004 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_5092 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_5092 v0 v1 v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RVar'45'poly_5092 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'poly_5092 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_5092 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RResolved'45'aux_4908
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Spec.Name.C_canonical_12
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.du_notGen'45'shape_686 erased)
              (coe
                 MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupImport_46
                 (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_sig_142 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Internal.Name.d_showCanonical_6
                    (coe
                       MAlonzo.Code.Once.Spec.Name.C_canonical_12
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> coe
                seq (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                         erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly-infer
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_5158 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_5158 ~v0 ~v1 v2
                                                      ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5158 v2
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5158 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5158 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_5200 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_5200 v0 v1 v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'id_5200 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'id_5200 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_5200 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614
              (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                               (coe MAlonzo.Code.Once.IR.C_id_20) v10 in
                     coe
                       (let v14 = addInt (coe (1 :: Integer)) (coe v11) in
                        coe
                          (let v15
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                     (coe v0) (coe v4) (coe v2) in
                           coe
                             (case coe v15 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                  -> if coe v16
                                       then case coe v17 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                        v4 v18 v13)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v14)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v17)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-fst
d_checkElab'45'fallback'45'RApp'45'fst_5290 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_5290 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'fst_5290 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'fst_5290 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_5290 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2584 (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v4) (coe v2) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v4
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-snd
d_checkElab'45'fallback'45'RApp'45'snd_5380 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_5380 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'snd_5380 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'snd_5380 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_5380 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2664 (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v4) (coe v2) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v4
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
-- Once.TypeCheck.ElaborateProofs.checkViewBridge
d_checkViewBridge_5460 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_5460 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_5488 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_5488 v0 v1 v2 v3 v4 v5
                                                ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RApp'45'generic_5488
      v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RApp'45'generic_5488 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_5488 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6752
              (coe v0) (coe v1) (coe v3) (coe v4)
              (coe
                 MAlonzo.Code.Once.Internal.Typing.Scope.d_classifyAppHeadView_352
                 (coe v3)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v9 v10 v11 v12 v13
                  -> let v14
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v5) (coe v2) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                            -> if coe v15
                                 then case coe v16 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v5
                                                  v17 v11)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v13) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v16)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferOutGo-J
d_inferOutGo'45'J_5592 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7522'_'8758'_'10814'__12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferOutGo'45'J_5592 = erased
-- Once.TypeCheck.ElaborateProofs.cata-go-canonical
d_cata'45'go'45'canonical_5628 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_5628 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-J
d_checkCataGo'45'J_5646 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'J_5646 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_5672 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_5672 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_5710 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'just'45'success_5710 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-J
d_checkAnaGo'45'J_5846 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'J_5846 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGoV-J
d_checkAnaGoV'45'J_5882 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGoV'45'J_5882 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-just-success
d_checkAnaGo'45'just'45'success_5936 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'just'45'success_5936 = erased
-- Once.TypeCheck.ElaborateProofs.checkLoopV-J
d_checkLoopV'45'J_6086 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkLoopV'45'J_6086 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_6122 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_6122 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_6206 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_6206 v0 v1 v2 v3 v4 ~v5
                                                 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'terminal_6206 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'terminal_6206 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_6206 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614
              (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v8
                               (coe MAlonzo.Code.Once.IR.C_terminal_72) v10 in
                     coe
                       (let v14 = addInt (coe (1 :: Integer)) (coe v11) in
                        coe
                          (let v15
                                 = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                                     (coe v0) (coe v4) (coe v2) in
                           coe
                             (case coe v15 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                  -> if coe v16
                                       then case coe v17 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                                                        v4 v18 v13)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v14)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v12) erased))
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else coe
                                              seq (coe v17)
                                              (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                _ -> MAlonzo.RTE.mazUnreachableError)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-Out
d_checkElab'45'fallback'45'RApp'45'Out_6296 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'Out_6296 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'Out_6296 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'Out_6296 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'Out_6296 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferOutOn_2504 (coe v0)
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v3)) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v4) (coe v2) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                            -> if coe v14
                                 then case coe v15 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v4
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RBinOp
d_checkElab'45'fallback'45'RBinOp_6390 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_6390 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RBinOp_6390 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RBinOp_6390 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_6390 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_3230
              (coe v0) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v4))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
                 (coe v1) (coe v5)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v9 v10 v11 v12 v13
                  -> let v14
                           = MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                               (coe v0) (coe v9) (coe v2) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                            -> if coe v15
                                 then case coe v16 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v9
                                                  v17 v11)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v13) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v16)
                                        (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExprTyped
d_compileExprTyped_6572 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_6572 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6634
                 (coe (0 :: Integer))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_330) (coe v0)
                 (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_1066
                   (0 :: Integer) (0 :: Integer)
                   (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12) v3 v1 v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.compileExpr
d_compileExpr_6596 ::
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_6596 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614
                 (coe (0 :: Integer))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyCtx_330)
                 (coe v0)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.d_elaborate'45'default_1066
                      (0 :: Integer) (0 :: Integer)
                      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12) v3 v2 v4))
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_100 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.inferElabProj
d_inferElabProj_6620 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_82
d_inferElabProj_6620 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6614 (coe v0)
         (coe v1) (coe v2))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_6638 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110
d_checkElabProj_6638 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6624 (coe v0)
         (coe v1) (coe v2) (coe v3))
