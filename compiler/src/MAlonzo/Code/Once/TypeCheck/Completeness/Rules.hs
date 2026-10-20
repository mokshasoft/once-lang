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

module MAlonzo.Code.Once.TypeCheck.Completeness.Rules where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Join
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Completeness.Rules.infer-complete-RInt
d_infer'45'complete'45'RInt_18 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RInt_18 ~v0 v1
  = du_infer'45'complete'45'RInt_18 v1
du_infer'45'complete'45'RInt_18 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RInt_18 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_190 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RUnit
d_infer'45'complete'45'RUnit_30 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnit_30 ~v0
  = du_infer'45'complete'45'RUnit_30
du_infer'45'complete'45'RUnit_30 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RUnit_30
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RVar-unit
d_infer'45'complete'45'RVar'45'unit_40 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'unit_40 ~v0
  = du_infer'45'complete'45'RVar'45'unit_40
du_infer'45'complete'45'RVar'45'unit_40 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'unit_40
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_158)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RResolved
d_infer'45'complete'45'RResolved_56 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved_56 ~v0 v1 v2 v3 ~v4 v5
  = du_infer'45'complete'45'RResolved_56 v1 v2 v3 v5
du_infer'45'complete'45'RResolved_56 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved_56 v0 v1 v2 v3
  = coe
      du_infer'45'complete'45'RResolved'45'view_84 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670 (coe v0))
      (coe v2) (coe v3)
-- Once.TypeCheck.Completeness.Rules.inferElabV-RResolved-J
d_inferElabV'45'RResolved'45'J_64 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RResolved'45'J_64 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RResolved-view
d_infer'45'complete'45'RResolved'45'view_84 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved'45'view_84 ~v0 v1 v2 v3 ~v4 v5 ~v6
                                            v7
  = du_infer'45'complete'45'RResolved'45'view_84 v1 v2 v3 v5 v7
du_infer'45'complete'45'RResolved'45'view_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved'45'view_84 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_620
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_622
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> coe
                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_624
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> coe
                           seq (coe v12) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_626
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> coe
                                  seq (coe v16) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_628
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> case coe v16 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                                    -> coe
                                         seq (coe v20)
                                         (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_630
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> case coe v16 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v23 v24
                                           -> coe
                                                seq (coe v24)
                                                (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_632
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> case coe v16 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v23 v24
                                           -> case coe v24 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v27 v28
                                                  -> coe
                                                       seq (coe v28)
                                                       (coe
                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_634
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> case coe v16 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v23 v24
                                           -> case coe v24 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v27 v28
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v31 v32
                                                         -> coe
                                                              seq (coe v32)
                                                              (coe
                                                                 MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_638 v6
        -> coe du_go_164 (coe v0) (coe v1) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules._.helper
d_helper_124 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_124 = erased
-- Once.TypeCheck.Completeness.Rules._.helperArr
d_helperArr_142 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperArr_142 = erased
-- Once.TypeCheck.Completeness.Rules._.helperVal
d_helperVal_152 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperVal_152 = erased
-- Once.TypeCheck.Completeness.Rules._.go
d_go_164 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_164 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
  = du_go_164 v1 v8 v9
du_go_164 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_164 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Void_12)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v1) (coe v2))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v1) (coe v2))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v11 v12
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedArrowTerm_4550
                                     (coe v3) (coe v5) (coe v0) (coe v7)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                           (coe v3) (coe v11)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                           (coe v5) (coe v12))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe (0 :: Integer)) erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Int_14)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v3 v4
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4630
                   (coe v0)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'rigid_32)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                      erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RResolved-own
d_infer'45'complete'45'RResolved'45'own_258 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved'45'own_258 ~v0 v1 ~v2 ~v3 ~v4
  = du_infer'45'complete'45'RResolved'45'own_258 v1
du_infer'45'complete'45'RResolved'45'own_258 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved'45'own_258 v0
  = coe
      du_view_298 (coe v0)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670
         (coe
            MAlonzo.Code.Once.Spec.Name.C_canonical_12
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.TypeCheck.Completeness.Rules._.h1
d_h1_280 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h1_280 = erased
-- Once.TypeCheck.Completeness.Rules._.h2
d_h2_288 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h2_288 = erased
-- Once.TypeCheck.Completeness.Rules._.view
d_view_298 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_view_298 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 = du_view_298 v1 v5
du_view_298 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_view_298 v0 v1
  = coe
      seq (coe v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v0)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
               erased)))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RPair
d_infer'45'complete'45'RPair_336 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RPair_336 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RPair_336 v0 v1 v2
du_infer'45'complete'45'RPair_336 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RPair_336 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                               (coe v0) (coe v2) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v14 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v7 v15 v8 v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9)
                                              (coe v17))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RUnaryOp-neg
d_infer'45'complete'45'RUnaryOp'45'neg_394 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnaryOp'45'neg_394 v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RUnaryOp'45'neg_394 v0 v1
du_infer'45'complete'45'RUnaryOp'45'neg_394 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RUnaryOp'45'neg_394 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_138
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_120
           -> case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_190
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_134
           -> let v4
                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                        (coe v0) (coe v1) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                     -> case coe v5 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                            -> coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe addInt (coe (1 :: Integer)) (coe v10))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                          erased)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RAnnot
d_infer'45'complete'45'RAnnot_464 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RAnnot_464 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_infer'45'complete'45'RAnnot_464 v0 v1 v2
du_infer'45'complete'45'RAnnot_464 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RAnnot_464 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v2) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                 (coe v0) (coe v1) (coe v2) in
       coe
         (coe
            seq (coe v3)
            (case coe v4 of
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                 -> case coe v5 of
                      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v7 v8 v9 v10
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
                      _ -> MAlonzo.RTE.mazUnreachableError
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RLet
d_infer'45'complete'45'RLet_526 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RLet_526 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                                ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RLet_526 v0 v1 v2 v3
du_infer'45'complete'45'RLet_526 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RLet_526 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                               (coe
                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                                  (coe v1) (coe v7))
                               (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v15 v16 v17 v18 v19
                                   -> case coe v16 of
                                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v21 v22
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v8
                                                  v22 v21 v7 v9 v17)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                     (coe v10)
                                                     (coe addInt (coe (1 :: Integer)) (coe v18)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v19) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-id
d_infer'45'complete'45'RApp'45'id_598 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'id_598 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'id_598 v0 v1
du_infer'45'complete'45'RApp'45'id_598 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'id_598 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_id_20) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-terminal
d_infer'45'complete'45'RApp'45'terminal_636 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'terminal_636 v0 v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'terminal_636 v0 v1
du_infer'45'complete'45'RApp'45'terminal_636 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'terminal_636 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_terminal_72) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-Out
d_infer'45'complete'45'RApp'45'Out_676 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'Out_676 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
                                       ~v8
  = du_infer'45'complete'45'RApp'45'Out_676 v0 v1 v2 v7
du_infer'45'complete'45'RApp'45'Out_676 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'Out_676 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v2)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                          (coe
                             MAlonzo.Code.Once.IR.C_Out_110
                             (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                (coe v2) (coe v3)))
                          v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v10))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-Out-act
d_infer'45'complete'45'RApp'45'Out'45'act_738 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'Out'45'act_738 v0 v1 v2 ~v3 ~v4 ~v5
                                              ~v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'Out'45'act_738 v0 v1 v2 v7
du_infer'45'complete'45'RApp'45'Out'45'act_738 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'Out'45'act_738 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v8
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v2)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                          (coe
                             MAlonzo.Code.Once.IR.C_curry_84
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__28
                                (coe
                                   MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                   (coe MAlonzo.Code.Once.IRTy.d_eraseF_50 (coe v2)))
                                (coe
                                   MAlonzo.Code.Once.IR.C_Out_110
                                   (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                      (coe v2) (coe v3)))
                                (coe MAlonzo.Code.Once.IR.C_fst_42)))
                          v9)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v10))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-fst
d_infer'45'complete'45'RApp'45'fst_800 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'fst_800 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'fst_800 v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'fst_800 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'fst_800 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3004
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v1))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                 (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v3))
                 (coe MAlonzo.Code.Once.IR.C_fst_42) v5)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe addInt (coe (1 :: Integer)) (coe v6))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased))))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-snd
d_infer'45'complete'45'RApp'45'snd_832 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'snd_832 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'snd_832 v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'snd_832 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'snd_832 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3004
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v1))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v4
                 (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v3))
                 (coe MAlonzo.Code.Once.IR.C_snd_48) v5)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe addInt (coe (1 :: Integer)) (coe v6))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased))))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-apply
d_infer'45'complete'45'RApp'45'apply_864 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'apply_864 v0 v1 v2 v3 v4 v5 v6 v7
                                         ~v8
  = du_infer'45'complete'45'RApp'45'apply_864 v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply_864 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply_864 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3004
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'pure_3036
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-apply-eff
d_infer'45'complete'45'RApp'45'apply'45'eff_906 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'apply'45'eff_906 v0 v1 v2 v3 v4 v5
                                                v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply'45'eff_906
      v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply'45'eff_906 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply'45'eff_906 v0 v1 v2 v3 v4 v5
                                                 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3004
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'eff_3074
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-apply-act
d_infer'45'complete'45'RApp'45'apply'45'act_948 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'apply'45'act_948 v0 v1 v2 v3 v4 v5
                                                v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply'45'act_948
      v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply'45'act_948 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply'45'act_948 v0 v1 v2 v3 v4 v5
                                                 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3004
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'act_3112
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RVar-local
d_infer'45'complete'45'RVar'45'local_984 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'local_984 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_infer'45'complete'45'RVar'45'local_984 v4
du_infer'45'complete'45'RVar'45'local_984 ::
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'local_984 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_558 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules._.helper
d_helper_1010 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_1010 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RVar-import
d_infer'45'complete'45'RVar'45'import_1024 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'import_1024 ~v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RVar'45'import_1024 v1
du_infer'45'complete'45'RVar'45'import_1024 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'import_1024 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules._.helperLoc
d_helperLoc_1052 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperLoc_1052 = erased
-- Once.TypeCheck.Completeness.Rules._.helperImp
d_helperImp_1058 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperImp_1058 = erased
-- Once.TypeCheck.Completeness.Rules._.helperImpVal
d_helperImpVal_1068 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperImpVal_1068 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-il′
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106 ~v0
                                                                 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                                                                 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v3 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v5) v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v3 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v5) v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v3 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v5) v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v3 v4
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v5) v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-il
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156 v0 v1
                                                           ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12
                                                           ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1156 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1106
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-ir′
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208 ~v0
                                                                 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                                                                 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208 v0
                                                                  v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v3 v4 v5
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v6))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v3 v4 v5
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v6))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v3 v4 v5
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v6))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v3 v4 v5
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v6))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-ir
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258 v0 v1
                                                           ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12
                                                           ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1258 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1208
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float′
d_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310 ~v0 v1
                                                           ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12
                                                           ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float
d_infer'45'complete'45'RBinOp'45'arith'45'float_1360 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float_1360 v0 v1 ~v2 v3
                                                     v4 v5 v6 v7 v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float_1360
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float_1360 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float_1360 v0 v1 v2 v3
                                                      v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1310
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith′
d_infer'45'complete'45'RBinOp'45'arith'8242'_1412 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'8242'_1412 ~v0 v1 ~v2 ~v3
                                                  ~v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'8242'_1412
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'8242'_1412 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'8242'_1412 v0 v1 v2 v3 v4
                                                   v5 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_add_208 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_div_286 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith
d_infer'45'complete'45'RBinOp'45'arith_1466 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith_1466 v0 v1 ~v2 v3 v4 v5 v6
                                            v7 v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith_1466
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith_1466 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith_1466 v0 v1 v2 v3 v4 v5 v6
                                             v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'8242'_1412 (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-cmp′
d_infer'45'complete'45'RBinOp'45'cmp'8242'_1518 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'cmp'8242'_1518 ~v0 v1 ~v2 ~v3 ~v4
                                                v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'cmp'8242'_1518
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'cmp'8242'_1518 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp'8242'_1518 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_le_324 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v3 v4 v5 v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v8))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-cmp
d_infer'45'complete'45'RBinOp'45'cmp_1576 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'cmp_1576 v0 v1 ~v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'cmp_1576
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'cmp_1576 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp_1576 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'cmp'8242'_1518 (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.decideLeq-just
d_decideLeq'45'just_1598 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decideLeq'45'just_1598 v0 v1 ~v2
  = du_decideLeq'45'just_1598 v0 v1
du_decideLeq'45'just_1598 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decideLeq'45'just_1598 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.TypeCheck.Completeness.Rules.check-complete-RLam
d_check'45'complete'45'RLam_1630 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete'45'RLam_1630 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
                                 ~v10 ~v11 ~v12 v13 ~v14
  = du_check'45'complete'45'RLam_1630 v0 v1 v2 v3 v4 v5 v6 v13
du_check'45'complete'45'RLam_1630 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam_1630 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
              (coe
                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v6) in
    coe
      (case coe v8 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
           -> case coe v9 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v11 v12 v13 v14
                  -> coe
                       seq (coe v11)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1302
                                  (coe v5) (coe v4) in
                        coe
                          (let v16 = coe du_decideLeq'45'just_1598 (coe v5) (coe v4) in
                           coe
                             (coe
                                seq (coe v15)
                                (coe
                                   seq (coe v16)
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2446
                                      (coe v7)
                                      (coe
                                         (\ v17 ->
                                            coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v5 v12)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe addInt (coe (1 :: Integer)) (coe v13))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v14) erased)))))))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RDestruct
d_infer'45'complete'45'RDestruct_1774 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8852'_'8788'__240 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RDestruct_1774 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                      ~v9 ~v10 ~v11 v12 v13 v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                      ~v22 ~v23 ~v24 ~v25 ~v26 ~v27 ~v28
  = du_infer'45'complete'45'RDestruct_1774
      v0 v1 v2 v3 v4 v5 v12 v13 v14
du_infer'45'complete'45'RDestruct_1774 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RDestruct_1774 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = let v9
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v9 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
           -> case coe v10 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v12 v13 v14 v15 v16
                  -> case coe v12 of
                       MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                         -> let v19
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                                      (coe
                                         MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132
                                         (coe v0) (coe v2) (coe v17))
                                      (coe v3) in
                            coe
                              (case coe v19 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                   -> case coe v20 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v22 v23 v24 v25 v26
                                          -> case coe v23 of
                                               MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v28 v29
                                                 -> let v30
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132
                                                                 (coe v0) (coe v4) (coe v18))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v30 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                           -> case coe v31 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v33 v34 v35 v36 v37
                                                                  -> case coe v34 of
                                                                       MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v39 v40
                                                                         -> coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_case''_152
                                                                                 v13 v29 v40 v28 v39
                                                                                 v17 v18 v14
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                                    v6
                                                                                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                                                                       (coe v6)
                                                                                       (coe v8)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Lang.Type.Sub.d_left_256
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Lang.Type.Join.d_sound_658
                                                                                             (coe
                                                                                                v6)
                                                                                             (coe
                                                                                                v7)
                                                                                             (coe
                                                                                                v8)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Lang.Type.Join.du_join'63''45'complete_850
                                                                                                   (coe
                                                                                                      v6)
                                                                                                   (coe
                                                                                                      v7))))))
                                                                                    v24)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_coerce_376
                                                                                    v7
                                                                                    (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''7580''8658''60''58'_190
                                                                                       (coe v7)
                                                                                       (coe v8)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Lang.Type.Sub.d_right_258
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Lang.Type.Join.d_sound_658
                                                                                             (coe
                                                                                                v6)
                                                                                             (coe
                                                                                                v7)
                                                                                             (coe
                                                                                                v8)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Lang.Type.Join.du_join'63''45'complete_850
                                                                                                   (coe
                                                                                                      v6)
                                                                                                   (coe
                                                                                                      v7))))))
                                                                                    v35))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                       (coe v15)
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe
                                                                                             v25)))
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v36)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v37)
                                                                                    erased))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-generic
d_infer'45'complete'45'RApp'45'generic_1944 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'generic_1944 v0 v1 v2 v3 ~v4 v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RApp'45'generic_1944 v0 v1 v2 v3 v5
du_infer'45'complete'45'RApp'45'generic_1944 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'generic_1944 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v14 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v16 v17 v18 v19
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_50 v9 v16 v3 v4
                                           v10 v17)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11)
                                              (coe v18))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.viewBridge
d_viewBridge_1956 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_AppHeadView_294 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_1956 = erased
-- Once.TypeCheck.Completeness.Rules.otherBridge
d_otherBridge_1968 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Lang.Typing.Scope.T_PolyBuiltinApp_260 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_otherBridge_1968 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-eff
d_infer'45'complete'45'RApp'45'eff_2072 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'eff_2072 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'eff_2072 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'eff_2072 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'eff_2072 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v8 v15 v3
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'eff_60) v9
                                           v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-act
d_infer'45'complete'45'RApp'45'act_2170 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'act_2170 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'act_2170 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'act_2170 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'act_2170 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6310
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v8 v15 v3
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'act_58) v9
                                           v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
