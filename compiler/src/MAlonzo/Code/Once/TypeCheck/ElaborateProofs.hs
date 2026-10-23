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
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.DualWitness
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
d_checkElab'45'fallback'45'RFloat_60 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RFloat_60 ~v0 ~v1 v2 v3 v4
  = du_checkElab'45'fallback'45'RFloat_60 v2 v3 v4
du_checkElab'45'fallback'45'RFloat_60 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RFloat_60 v0 v1 v2
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
d_checkElab'45'fallback'45'RUnit_108 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_108 ~v0 ~v1
  = du_checkElab'45'fallback'45'RUnit_108
du_checkElab'45'fallback'45'RUnit_108 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnit_108
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
d_checkElab'45'fallback'45'RResolved_152 ::
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
d_checkElab'45'fallback'45'RResolved_152 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                         ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RResolved_152 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RResolved_152 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RResolved_152 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_692
              (coe v3) in
    coe
      (let v6
             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV'45'RResolved'45'dispatch_5880
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
d_checkElab'45'fallback'45'RAnnot_1004 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_1004 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RAnnot_1004 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RAnnot_1004 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_1004 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2998
              (coe v0) (coe v4)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6448
                 (coe v0) (coe v1) (coe v3)
                 (coe
                    MAlonzo.Code.Once.Internal.Type.d_wk'8320'_12 (coe v0)
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
                                  (\ v13 -> coe MAlonzo.Code.Once.Internal.Type.du_none_8))
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
                                                          MAlonzo.Code.Once.Internal.Type.du_none_8))
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
d_checkElab'45'fallback'45'RLet_1184 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_1184 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                     ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RLet_1184 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RLet_1184 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_1184 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_6496
              (coe v0) (coe v1) (coe v3) (coe v5)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkElab'45'fallback'45'RDestruct_1396 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_1396 v0 v1 v2 v3 v4 v5 v6 v7
                                          ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_checkElab'45'fallback'45'RDestruct_1396
      v0 v1 v2 v3 v4 v5 v6 v7
du_checkElab'45'fallback'45'RDestruct_1396 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_1396 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_6512
              (coe v0) (coe v1) (coe v4) (coe v5) (coe v6) (coe v7)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RNeg
d_checkElab'45'fallback'45'RNeg_1626 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RNeg_1626 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                     ~v8
  = du_checkElab'45'fallback'45'RNeg_1626 v0 v1 v2 v3
du_checkElab'45'fallback'45'RNeg_1626 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RNeg_1626 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_150
              (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_134
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                          (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                          (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v6)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_142
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v8 v9 v10
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
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_146
           -> let v6
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RNeg'45'aux_3030
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RNeg-sub
d_checkElab'45'fallback'45'RNeg'45'sub_1858 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RNeg'45'sub_1858 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 v10
  = du_checkElab'45'fallback'45'RNeg'45'sub_1858 v0 v1 v2 v3 v4 v10
du_checkElab'45'fallback'45'RNeg'45'sub_1858 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RNeg'45'sub_1858 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_150
              (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_134
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v8
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380
                             (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                             (coe MAlonzo.Code.Once.Spec.Sub.C_sub'45'int_22)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_neg_308
                                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (2 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'float_142
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v10 v11 v12
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
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_146
           -> let v8
                    = coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RNeg'45'aux_3030
                        (coe v0)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 v0 v1 v2 v3
                                                       v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182
      v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 v0 v1 v2 v3
                                                        v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferApplyOn_2910 (coe v0)
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkElab'45'fallback'45'RVar'45'unit_2258 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_2258 ~v0 ~v1
  = du_checkElab'45'fallback'45'RVar'45'unit_2258
du_checkElab'45'fallback'45'RVar'45'unit_2258 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'unit_2258
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
d_inferElabV'45'own'45'poly'45'bridge_2288 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'own'45'poly'45'bridge_2288 = erased
-- Once.TypeCheck.ElaborateProofs._.own-dispatch
d_own'45'dispatch_2304 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_own'45'dispatch_2304 = erased
-- Once.TypeCheck.ElaborateProofs._._.sig-eq
d_sig'45'eq_2316 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig'45'eq_2316 = erased
-- Once.TypeCheck.ElaborateProofs._._.imp-eq
d_imp'45'eq_2322 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_imp'45'eq_2322 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-lookup-eq
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2338 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'lookup'45'eq_2338 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-ground-eq
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2368 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'ground'45'eq_2368 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nothing
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2394 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nothing_2394
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-fail-nonground
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2420 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'fail'45'nonground_2420
  = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-RVar-poly-aux-success
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2456 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RVar'45'poly'45'aux'45'success_2456 = erased
-- Once.TypeCheck.ElaborateProofs.inferElabV-own-fail-bridge
d_inferElabV'45'own'45'fail'45'bridge_2486 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'own'45'fail'45'bridge_2486 = erased
-- Once.TypeCheck.ElaborateProofs.withUnit-elim
d_withUnit'45'elim_2512 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
d_withUnit'45'elim_2512 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_withUnit'45'elim_2512 v3 v6
du_withUnit'45'elim_2512 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  (MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 -> AgdaAny) -> AgdaAny
du_withUnit'45'elim_2512 v0 v1 = coe seq (coe v0) (coe v1 v0)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_2554 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_2554 v0 ~v1 ~v2 v3 v4
  = du_checkElab'45'fallback'45'RVar'45'id_2554 v0 v3 v4
du_checkElab'45'fallback'45'RVar'45'id_2554 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_2554 v0 v1 v2
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
                          du_withUnit'45'elim_2512 (coe v2)
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
d_just'8802'nothing'45'Maybe_2594 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing'45'Maybe_2594 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_2614 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_2614 v0 ~v1 ~v2 v3 ~v4 v5
  = du_checkElab'45'fallback'45'RVar'45'fst_2614 v0 v3 v5
du_checkElab'45'fallback'45'RVar'45'fst_2614 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_2614 v0 v1 v2
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
                          du_withUnit'45'elim_2512 (coe v2)
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
d_checkElab'45'fallback'45'RVar'45'snd_2674 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_2674 v0 ~v1 ~v2 ~v3 v4 v5
  = du_checkElab'45'fallback'45'RVar'45'snd_2674 v0 v4 v5
du_checkElab'45'fallback'45'RVar'45'snd_2674 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_2674 v0 v1 v2
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
                          du_withUnit'45'elim_2512 (coe v2)
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
d_checkElab'45'fallback'45'RVar'45'terminal_2732 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_2732 ~v0 ~v1 ~v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'terminal_2732 v4
du_checkElab'45'fallback'45'RVar'45'terminal_2732 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_2732 v0
  = coe
      du_withUnit'45'elim_2512 (coe v0)
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
d_checkElab'45'fallback'45'RVar'45'terminalV_2768 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminalV_2768 ~v0 ~v1 ~v2 v3 v4
  = du_checkElab'45'fallback'45'RVar'45'terminalV_2768 v3 v4
du_checkElab'45'fallback'45'RVar'45'terminalV_2768 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminalV_2768 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
        -> coe
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
                         MAlonzo.Code.Once.TypeCheck.DualWitness.du_dt'45'terminal'45'morph'45'check_714
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_fin_42
                            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                         (coe v1))
                      erased)))
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe
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
                         MAlonzo.Code.Once.TypeCheck.DualWitness.du_dt'45'terminal'45'morph'45'check_714
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Spec.Grade.C_fin_42
                            (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                         (coe v1))
                      erased)))
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe
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
                         MAlonzo.Code.Once.TypeCheck.DualWitness.du_dt'45'terminal'45'morph'45'check_714
                         (coe v0) (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44) (coe v1))
                      erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_2798 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_2798 ~v0 ~v1 ~v2 ~v3 v4
  = du_checkElab'45'fallback'45'RVar'45'initial_2798 v4
du_checkElab'45'fallback'45'RVar'45'initial_2798 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_2798 v0
  = coe
      du_withUnit'45'elim_2512 (coe v0)
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
d_checkElab'45'fallback'45'RVar'45'inl_2834 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_2834 v0 ~v1 ~v2 v3 ~v4 v5
  = du_checkElab'45'fallback'45'RVar'45'inl_2834 v0 v3 v5
du_checkElab'45'fallback'45'RVar'45'inl_2834 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_2834 v0 v1 v2
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
                          du_withUnit'45'elim_2512 (coe v2)
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
d_checkElab'45'fallback'45'RVar'45'inr_2894 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_2894 v0 ~v1 ~v2 ~v3 v4 v5
  = du_checkElab'45'fallback'45'RVar'45'inr_2894 v0 v4 v5
du_checkElab'45'fallback'45'RVar'45'inr_2894 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_2894 v0 v1 v2
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
                          du_withUnit'45'elim_2512 (coe v2)
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
d_checkInGo'45'J_2948 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkInGo'45'J_2948 = erased
-- Once.TypeCheck.ElaborateProofs.checkInGo-just-success
d_checkInGo'45'just'45'success_2982 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo'45'just'45'success_2982 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8
                                    ~v9 ~v10
  = du_checkInGo'45'just'45'success_2982 v0 v1 v2 v3 v4
du_checkInGo'45'just'45'success_2982 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo'45'just'45'success_2982 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6448
              (coe v0) (coe v1) (coe v2)
              (coe
                 MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v3)
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
d_checkElab'45'fallback'45'RApp'45'In_3036 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'In_3036 v0 v1 v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'In_3036 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'In_3036 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'In_3036 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_checkInGo'45'just'45'success_2982 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_checkInGo'45'just'45'success_2982 (coe v0) (coe v1) (coe v2)
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
                        du_checkInGo'45'just'45'success_2982 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4)))))
            erased))
-- Once.TypeCheck.ElaborateProofs.via
d_via_3094 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
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
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_via_3094 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 v15
  = du_via_3094 v6 v15
du_via_3094 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_via_3094 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe seq (coe v2) (coe v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.apply-pure
d_apply'45'pure_3128 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'pure_3128 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'pure_3128 v0 v3 v4 v5 v6 v7 v8
du_apply'45'pure_3128 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'pure_3128 v0 v1 v2 v3 v4 v5 v6
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
d_apply'45'eff_3168 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'eff_3168 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'eff_3168 v0 v3 v4 v5 v6 v7 v8
du_apply'45'eff_3168 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'eff_3168 v0 v1 v2 v3 v4 v5 v6
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
d_apply'45'act_3208 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply'45'act_3208 v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_apply'45'act_3208 v0 v3 v4 v5 v6 v7 v8
du_apply'45'act_3208 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_apply'45'act_3208 v0 v1 v2 v3 v4 v5 v6
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
d_checkElab'45'fallback'45'RApp'45'apply_3248 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_3248 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply_3248
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply_3248 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_3248 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8 v9
  = let v10
          = coe
              du_via_3094
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'pure_3128 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 (coe v0)
                          (coe v1) (coe v2) (coe v3) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-apply-effclosure
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3326 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3326 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3326
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3326 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'effclosure_3326 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = coe
              du_via_3094
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'eff_3168 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 (coe v0)
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
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3404 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3404 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3404
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3404 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply'45'actclosure_3404 v0 v1
                                                             v2 v3 v4 v5 v6 v7 v8 v9
  = let v10
          = coe
              du_via_3094
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
                 (coe v1) (coe v3))
              (\ v10 ->
                 coe
                   du_apply'45'act_3208 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7)
                   (coe v8) (coe v9)) in
    coe
      (case coe v10 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
           -> case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v14)
                       (coe
                          du_checkElab'45'fallback'45'RApp'45'apply'45'infer_2182 (coe v0)
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
d_resolveExprWF_3468 ::
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
d_resolveExprWF_3468 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_resolveExprWF_3468 v0 v4 v5 v7 v8 v9 v10
du_resolveExprWF_3468 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExprWF_3468 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_20 v9
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v10
                    (coe
                       du_resolveExprWF_3468 (coe v0) (coe v19) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_54 v9 v10 v11 v13
             (coe
                du_resolveExprWF_3468 (coe v0)
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
                du_resolveExprWF_3468 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v9 v10 v11 v14
                           (coe
                              du_resolveExprWF_3468 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_3468 (coe v0) (coe v11) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v9 v10
                    (coe
                       du_resolveExprWF_3468 (coe v0) (coe v15) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v13))
                    (coe
                       du_resolveExprWF_3468 (coe v0) (coe v16) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v11
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v1) (coe v11))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v10) (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_122
                    (coe
                       du_resolveExprWF_3468 (coe v0) (coe v13) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_134
                    (coe
                       du_resolveExprWF_3468 (coe v0) (coe v14) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v9 v10 v11 v12 v13
             v14 v15
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v17))
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v18))
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v19))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_162
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_162
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_172
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v9 v10 v11 v12
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v12) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v14))
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_194 v9
      MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_float_202 v9
      MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_212 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_222 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_232 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fadd_242 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fsub_252 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fmul_262 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_272 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_280 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_i2f_280
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_290 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_300 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_308 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_308
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_318 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_328 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_338 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_348 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_368 v9 v10
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v11))
             (coe
                du_resolveExprWF_3468 (coe v0)
                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_coerce_380 v10 v12
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_388 v9 v10 v11
      MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_closure_396 v10
      MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v9
        -> coe
             du_resolvePolyCase_3484 (coe v0) (coe v3) (coe v4) (coe v5)
             (coe v9) (coe v1)
             (coe
                MAlonzo.Code.Once.Internal.Typing.Scope.d_lookupPolyPrefix_76
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_closed_414 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_closed_414
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_426 v12
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_438 v9 v10 v12
             (coe
                du_resolveExprWF_3468 (coe v0) (coe v10) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_comp''_456 v9 v10 v12
                           (coe
                              du_resolveExprWF_3468 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                 (coe v19))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                           (coe
                              du_resolveExprWF_3468 (coe v0)
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
                                     du_resolveExprWF_3468 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v23))
                                        (coe v19))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_3468 (coe v0)
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
                                     du_resolveExprWF_3468 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v21))
                                        (coe v22))
                                     (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
                                  (coe
                                     du_resolveExprWF_3468 (coe v0)
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
                                     du_resolveExprWF_3468 (coe v0)
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
                                     du_resolveExprWF_3468 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v19) (coe v18))
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
                              du_resolveExprWF_3468 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v17)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v21)))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v20)
                                    (coe v17)))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_loop_556 v9
                    (coe
                       du_resolveExprWF_3468 (coe v0)
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
d_resolvePolyCase_3484 ::
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
d_resolvePolyCase_3484 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 ~v11
  = du_resolvePolyCase_3484 v0 v5 v6 v7 v8 v9 v10
du_resolvePolyCase_3484 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolvePolyCase_3484 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe
                           du_applySplice_3506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v10) (coe v11)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6438 (coe v0)
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
d_applySplice_3506 ::
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
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_applySplice_3506 v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 ~v10 v11 v12
                   ~v13 v14
  = du_applySplice_3506 v0 v5 v6 v7 v8 v9 v11 v12 v14
du_applySplice_3506 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_applySplice_3506 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v11 v12 v13 v14
               -> coe
                    seq (coe v11)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_414
                       (coe
                          du_resolveExprWF_3468 (coe v0) (coe v5) (coe v7) (coe v1) (coe v2)
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
                             (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v11
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ElaborateProofs.resolveExpr
d_resolveExpr_4170 ::
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
d_resolveExpr_4170 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_resolveExpr_4170 v0 v4 v5 v6 v7 v8 v9
du_resolveExpr_4170 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
du_resolveExpr_4170 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_resolveExprWF_3468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6)
-- Once.TypeCheck.ElaborateProofs.resolveExpr-var
d_resolveExpr'45'var_4198 ::
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
d_resolveExpr'45'var_4198 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lam
d_resolveExpr'45'lam_4230 ::
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
d_resolveExpr'45'lam_4230 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-app
d_resolveExpr'45'app_4260 ::
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
d_resolveExpr'45'app_4260 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-pair
d_resolveExpr'45'pair_4288 ::
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
d_resolveExpr'45'pair_4288 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-effApp
d_resolveExpr'45'effApp_4320 ::
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
d_resolveExpr'45'effApp_4320 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-fst'
d_resolveExpr'45'fst''_4344 ::
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
d_resolveExpr'45'fst''_4344 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-snd'
d_resolveExpr'45'snd''_4368 ::
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
d_resolveExpr'45'snd''_4368 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inl'
d_resolveExpr'45'inl''_4392 ::
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
d_resolveExpr'45'inl''_4392 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-inr'
d_resolveExpr'45'inr''_4416 ::
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
d_resolveExpr'45'inr''_4416 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-case'
d_resolveExpr'45'case''_4454 ::
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
d_resolveExpr'45'case''_4454 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-unit
d_resolveExpr'45'unit_4470 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_4470 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-absurd
d_resolveExpr'45'absurd_4492 ::
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
d_resolveExpr'45'absurd_4492 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-let'
d_resolveExpr'45'let''_4522 ::
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
d_resolveExpr'45'let''_4522 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-int
d_resolveExpr'45'int_4540 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_4540 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-add
d_resolveExpr'45'add_4564 ::
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
d_resolveExpr'45'add_4564 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sub
d_resolveExpr'45'sub_4588 ::
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
d_resolveExpr'45'sub_4588 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mul
d_resolveExpr'45'mul_4612 ::
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
d_resolveExpr'45'mul_4612 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-div
d_resolveExpr'45'div_4636 ::
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
d_resolveExpr'45'div_4636 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-mod'
d_resolveExpr'45'mod''_4660 ::
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
d_resolveExpr'45'mod''_4660 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-neg
d_resolveExpr'45'neg_4680 ::
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
d_resolveExpr'45'neg_4680 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-lt
d_resolveExpr'45'lt_4704 ::
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
d_resolveExpr'45'lt_4704 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-le
d_resolveExpr'45'le_4728 ::
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
d_resolveExpr'45'le_4728 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-gt
d_resolveExpr'45'gt_4752 ::
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
d_resolveExpr'45'gt_4752 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ge
d_resolveExpr'45'ge_4776 ::
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
d_resolveExpr'45'ge_4776 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-eq
d_resolveExpr'45'eq_4800 ::
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
d_resolveExpr'45'eq_4800 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-ne
d_resolveExpr'45'ne_4824 ::
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
d_resolveExpr'45'ne_4824 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-coerce
d_resolveExpr'45'coerce_4850 ::
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
d_resolveExpr'45'coerce_4850 = erased
-- Once.TypeCheck.ElaborateProofs.resolveExpr-sigOp-extern
d_resolveExpr'45'sigOp'45'extern_4872 ::
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
d_resolveExpr'45'sigOp'45'extern_4872 = erased
-- Once.TypeCheck.ElaborateProofs.poly-check-eq
d_poly'45'check'45'eq_4900 ::
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
d_poly'45'check'45'eq_4900 = erased
-- Once.TypeCheck.ElaborateProofs.poly-ground-eq
d_poly'45'ground'45'eq_4936 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'ground'45'eq_4936 = erased
-- Once.TypeCheck.ElaborateProofs.poly-inst-yes
d_poly'45'inst'45'yes_4978 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'inst'45'yes_4978 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_5066 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_5066 v0 v1 v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_checkElab'45'fallback'45'RVar'45'poly_5066 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'poly_5066 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_5066 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RResolved'45'aux_4796
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
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_5132 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly'45'infer_5132 ~v0 ~v1 v2
                                                      ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5132 v2
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5132 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly'45'infer_5132 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_406 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_5174 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_5174 v0 v1 v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'id_5174 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'id_5174 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_5174 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428
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
d_checkElab'45'fallback'45'RApp'45'fst_5264 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_5264 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'fst_5264 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'fst_5264 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_5264 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferFstOn_2576 (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkElab'45'fallback'45'RApp'45'snd_5354 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_5354 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'snd_5354 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'snd_5354 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_5354 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferSndOn_2656 (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkViewBridge_5434 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_AppHeadView_306 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkViewBridge_5434 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_5462 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_5462 v0 v1 v2 v3 v4 v5
                                                ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RApp'45'generic_5462
      v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RApp'45'generic_5462 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_5462 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RApp'45'dispatch_6566
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
d_inferOutGo'45'J_5566 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferOutGo'45'J_5566 = erased
-- Once.TypeCheck.ElaborateProofs.cata-go-canonical
d_cata'45'go'45'canonical_5602 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'go'45'canonical_5602 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-J
d_checkCataGo'45'J_5620 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'J_5620 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGoV-pure-J
d_checkCataGoV'45'pure'45'J_5646 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGoV'45'pure'45'J_5646 = erased
-- Once.TypeCheck.ElaborateProofs.checkCataGo-just-success
d_checkCataGo'45'just'45'success_5684 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCataGo'45'just'45'success_5684 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-J
d_checkAnaGo'45'J_5820 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'J_5820 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGoV-J
d_checkAnaGoV'45'J_5856 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGoV'45'J_5856 = erased
-- Once.TypeCheck.ElaborateProofs.checkAnaGo-just-success
d_checkAnaGo'45'just'45'success_5910 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
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
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkAnaGo'45'just'45'success_5910 = erased
-- Once.TypeCheck.ElaborateProofs.checkLoopV-J
d_checkLoopV'45'J_6060 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkLoopV'45'J_6060 = erased
-- Once.TypeCheck.ElaborateProofs.checkCata-eff-strong-hlp
d_checkCata'45'eff'45'strong'45'hlp_6096 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkCata'45'eff'45'strong'45'hlp_6096 = erased
-- Once.TypeCheck.ElaborateProofs.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_6180 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_6180 v0 v1 v2 v3 v4 ~v5
                                                 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'terminal_6180 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'terminal_6180 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_6180 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428
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
d_checkElab'45'fallback'45'RApp'45'Out_6270 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'Out_6270 v0 v1 v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10
  = du_checkElab'45'fallback'45'RApp'45'Out_6270 v0 v1 v2 v3 v4
du_checkElab'45'fallback'45'RApp'45'Out_6270 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'Out_6270 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferOutOn_2496 (coe v0)
              (coe v1)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_checkElab'45'fallback'45'RBinOp_6364 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_6364 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                       ~v8 ~v9 ~v10 ~v11 ~v12
  = du_checkElab'45'fallback'45'RBinOp_6364 v0 v1 v2 v3 v4 v5
du_checkElab'45'fallback'45'RBinOp_6364 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_BinOp_44 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_6364 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_3204
              (coe v0) (coe v3)
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
                 (coe v1) (coe v4))
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
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
d_compileExprTyped_6546 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_compileExprTyped_6546 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6448
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
d_compileExpr_6570 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_6570 v0
  = let v1
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428
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
d_inferElabProj_6594 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_82
d_inferElabProj_6594 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6428 (coe v0)
         (coe v1) (coe v2))
-- Once.TypeCheck.ElaborateProofs.checkElabProj
d_checkElabProj_6612 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110
d_checkElabProj_6612 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6438 (coe v0)
         (coe v1) (coe v2) (coe v3))
