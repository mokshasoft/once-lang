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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
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
-- Once.TypeCheck.Completeness.Rules.infer-complete-RQualified
d_infer'45'complete'45'RQualified_56 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RQualified_56 ~v0 v1 v2 v3 ~v4 v5
  = du_infer'45'complete'45'RQualified_56 v1 v2 v3 v5
du_infer'45'complete'45'RQualified_56 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RQualified_56 v0 v1 v2 v3
  = coe du_go_118 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Completeness.Rules._.helper
d_helper_78 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_78 = erased
-- Once.TypeCheck.Completeness.Rules._.helperArr
d_helperArr_96 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
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
d_helperArr_96 = erased
-- Once.TypeCheck.Completeness.Rules._.helperVal
d_helperVal_106 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperVal_106 = erased
-- Once.TypeCheck.Completeness.Rules._.go
d_go_118 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_118 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 = du_go_118 v1 v2 v6 v7
du_go_118 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_118 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
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
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Void_12)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                              (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v0)))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v2) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                              (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v0)))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v2) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                 erased))
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> case coe v3 of
                           MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422
                                     (coe
                                        MAlonzo.Code.Once.IR.C_SigOp_132 (coe v4) (coe v6)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_ext'45'arrow'45'info_4406
                                           (coe v6) (coe v1) (coe v0) (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                                 (coe v4) (coe v12)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                                 (coe v6) (coe v13))))))
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
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
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
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v0)))
                (coe
                   MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                   (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Float_16)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   erased))
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v4 v5
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                   (MAlonzo.Code.Once.Spec.Name.d_bare_14
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("." :: Data.Text.Text) v0)))
                   (coe
                      MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38
                      (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'rigid_32)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                      erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules.infer-complete-RResolved
d_infer'45'complete'45'RResolved_202 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved_202 ~v0 v1 v2 v3 ~v4 v5
  = du_infer'45'complete'45'RResolved_202 v1 v2 v3 v5
du_infer'45'complete'45'RResolved_202 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved_202 v0 v1 v2 v3
  = coe
      du_infer'45'complete'45'RResolved'45'view_230 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670 (coe v0))
      (coe v2) (coe v3)
-- Once.TypeCheck.Completeness.Rules.inferElabV-RResolved-J
d_inferElabV'45'RResolved'45'J_210 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElabV'45'RResolved'45'J_210 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RResolved-view
d_infer'45'complete'45'RResolved'45'view_230 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved'45'view_230 ~v0 v1 v2 v3 ~v4 v5
                                             ~v6 v7
  = du_infer'45'complete'45'RResolved'45'view_230 v1 v2 v3 v5 v7
du_infer'45'complete'45'RResolved'45'view_230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved'45'view_230 v0 v1 v2 v3 v4
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
        -> coe du_go_310 (coe v0) (coe v1) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.Rules._.helper
d_helper_270 ::
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
d_helper_270 = erased
-- Once.TypeCheck.Completeness.Rules._.helperArr
d_helperArr_288 ::
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
d_helperArr_288 = erased
-- Once.TypeCheck.Completeness.Rules._.helperVal
d_helperVal_298 ::
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
d_helperVal_298 = erased
-- Once.TypeCheck.Completeness.Rules._.go
d_go_310 ::
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
d_go_310 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
  = du_go_310 v1 v8 v9
du_go_310 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_310 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedArrowTerm_4610
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_resolvedValueTerm_4690
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
d_infer'45'complete'45'RResolved'45'own_404 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved'45'own_404 ~v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_infer'45'complete'45'RResolved'45'own_404 v1
du_infer'45'complete'45'RResolved'45'own_404 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved'45'own_404 v0
  = coe
      du_view_452 (coe v0)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_670
         (coe
            MAlonzo.Code.Once.Spec.Name.C_canonical_12
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.TypeCheck.Completeness.Rules._.h1
d_h1_428 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h1_428 = erased
-- Once.TypeCheck.Completeness.Rules._.h2
d_h2_436 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h2_436 = erased
-- Once.TypeCheck.Completeness.Rules._.h3
d_h3_442 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_h3_442 = erased
-- Once.TypeCheck.Completeness.Rules._.view
d_view_452 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_view_452 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 = du_view_452 v1 v6
du_view_452 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_618 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_view_452 v0 v1
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
d_infer'45'complete'45'RPair_490 ::
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
d_infer'45'complete'45'RPair_490 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RPair_490 v0 v1 v2
du_infer'45'complete'45'RPair_490 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RPair_490 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
d_infer'45'complete'45'RUnaryOp'45'neg_548 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnaryOp'45'neg_548 v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RUnaryOp'45'neg_548 v0 v1
du_infer'45'complete'45'RUnaryOp'45'neg_548 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RUnaryOp'45'neg_548 v0 v1
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
                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
d_infer'45'complete'45'RAnnot_618 ::
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
d_infer'45'complete'45'RAnnot_618 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_infer'45'complete'45'RAnnot_618 v0 v1 v2
du_infer'45'complete'45'RAnnot_618 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RAnnot_618 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v2) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6392
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
d_infer'45'complete'45'RLet_680 ::
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
d_infer'45'complete'45'RLet_680 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                                ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RLet_680 v0 v1 v2 v3
du_infer'45'complete'45'RLet_680 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RLet_680 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
d_infer'45'complete'45'RApp'45'id_752 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'id_752 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'id_752 v0 v1
du_infer'45'complete'45'RApp'45'id_752 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'id_752 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
d_infer'45'complete'45'RApp'45'terminal_790 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'terminal_790 v0 v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'terminal_790 v0 v1
du_infer'45'complete'45'RApp'45'terminal_790 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'terminal_790 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
d_infer'45'complete'45'RApp'45'Out_830 ::
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
d_infer'45'complete'45'RApp'45'Out_830 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 v7
                                       ~v8
  = du_infer'45'complete'45'RApp'45'Out_830 v0 v1 v2 v7
du_infer'45'complete'45'RApp'45'Out_830 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'Out_830 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
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
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-Out-eff
d_infer'45'complete'45'RApp'45'Out'45'eff_892 ::
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
d_infer'45'complete'45'RApp'45'Out'45'eff_892 v0 v1 v2 ~v3 ~v4 ~v5
                                              ~v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'Out'45'eff_892 v0 v1 v2 v7
du_infer'45'complete'45'RApp'45'Out'45'eff_892 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'Out'45'eff_892 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
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
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-Out-act
d_infer'45'complete'45'RApp'45'Out'45'act_916 ::
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
d_infer'45'complete'45'RApp'45'Out'45'act_916 v0 v1 v2 ~v3 ~v4 ~v5
                                              ~v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'Out'45'act_916 v0 v1 v2 v7
du_infer'45'complete'45'RApp'45'Out'45'act_916 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'Out'45'act_916 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
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
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
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
d_infer'45'complete'45'RApp'45'fst_1016 ::
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
d_infer'45'complete'45'RApp'45'fst_1016 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'fst_1016 v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'fst_1016 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'fst_1016 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3194
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
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
d_infer'45'complete'45'RApp'45'snd_1048 ::
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
d_infer'45'complete'45'RApp'45'snd_1048 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'snd_1048 v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'snd_1048 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'snd_1048 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3194
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
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
d_infer'45'complete'45'RApp'45'apply_1080 ::
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
d_infer'45'complete'45'RApp'45'apply_1080 v0 v1 v2 v3 v4 v5 v6 v7
                                          ~v8
  = du_infer'45'complete'45'RApp'45'apply_1080
      v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply_1080 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply_1080 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3194
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'pure_3226
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-apply-eff
d_infer'45'complete'45'RApp'45'apply'45'eff_1122 ::
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
d_infer'45'complete'45'RApp'45'apply'45'eff_1122 v0 v1 v2 v3 v4 v5
                                                 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply'45'eff_1122
      v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply'45'eff_1122 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply'45'eff_1122 v0 v1 v2 v3 v4 v5
                                                  v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3194
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'eff_3264
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-apply-act
d_infer'45'complete'45'RApp'45'apply'45'act_1164 ::
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
d_infer'45'complete'45'RApp'45'apply'45'act_1164 v0 v1 v2 v3 v4 v5
                                                 v6 v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply'45'act_1164
      v0 v1 v2 v3 v4 v5 v6 v7
du_infer'45'complete'45'RApp'45'apply'45'act_1164 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply'45'act_1164 v0 v1 v2 v3 v4 v5
                                                  v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_via_3194
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v1))
      (\ v8 ->
         coe
           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_apply'45'act_3302
           (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.TypeCheck.Completeness.Rules.infer-complete-RVar-local
d_infer'45'complete'45'RVar'45'local_1200 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'local_1200 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_infer'45'complete'45'RVar'45'local_1200 v4
du_infer'45'complete'45'RVar'45'local_1200 ::
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'local_1200 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_546 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules._.helper
d_helper_1226 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_SVar_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_1226 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RVar-import
d_infer'45'complete'45'RVar'45'import_1240 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'import_1240 ~v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RVar'45'import_1240 v1
du_infer'45'complete'45'RVar'45'import_1240 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'import_1240 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
            erased))
-- Once.TypeCheck.Completeness.Rules._.helperLoc
d_helperLoc_1268 ::
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
d_helperLoc_1268 = erased
-- Once.TypeCheck.Completeness.Rules._.helperImp
d_helperImp_1274 ::
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
d_helperImp_1274 = erased
-- Once.TypeCheck.Completeness.Rules._.helperImpVal
d_helperImpVal_1284 ::
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
d_helperImpVal_1284 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-il′
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322 ~v0
                                                                 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                                                                 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322 v0
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1372 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1372 v0 v1
                                                           ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12
                                                           ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1372
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1372 ::
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
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1372 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il'8242'_1322
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float-ir′
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424 ~v0
                                                                 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                                                                 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424 v0
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1474 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1474 v0 v1
                                                           ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11 v12
                                                           ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1474
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1474 ::
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
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1474 v0 v1
                                                            v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir'8242'_1424
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith-float′
d_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526 ~v0 v1
                                                           ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12
                                                           ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526 v0 v1
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
d_infer'45'complete'45'RBinOp'45'arith'45'float_1576 ::
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
d_infer'45'complete'45'RBinOp'45'arith'45'float_1576 v0 v1 ~v2 v3
                                                     v4 v5 v6 v7 v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float_1576
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith'45'float_1576 ::
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
du_infer'45'complete'45'RBinOp'45'arith'45'float_1576 v0 v1 v2 v3
                                                      v4 v5 v6 v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'45'float'8242'_1526
      (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-arith′
d_infer'45'complete'45'RBinOp'45'arith'8242'_1628 ::
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
d_infer'45'complete'45'RBinOp'45'arith'8242'_1628 ~v0 v1 ~v2 ~v3
                                                  ~v4 v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'arith'8242'_1628
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'arith'8242'_1628 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'8242'_1628 v0 v1 v2 v3 v4
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
d_infer'45'complete'45'RBinOp'45'arith_1682 ::
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
d_infer'45'complete'45'RBinOp'45'arith_1682 v0 v1 ~v2 v3 v4 v5 v6
                                            v7 v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith_1682
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'arith_1682 ::
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
du_infer'45'complete'45'RBinOp'45'arith_1682 v0 v1 v2 v3 v4 v5 v6
                                             v7 v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'arith'8242'_1628 (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.infer-complete-RBinOp-cmp′
d_infer'45'complete'45'RBinOp'45'cmp'8242'_1734 ::
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
d_infer'45'complete'45'RBinOp'45'cmp'8242'_1734 ~v0 v1 ~v2 ~v3 ~v4
                                                v5 v6 v7 v8 v9 v10 v11 v12 ~v13 v14 ~v15 ~v16
  = du_infer'45'complete'45'RBinOp'45'cmp'8242'_1734
      v1 v5 v6 v7 v8 v9 v10 v11 v12 v14
du_infer'45'complete'45'RBinOp'45'cmp'8242'_1734 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp'8242'_1734 v0 v1 v2 v3 v4 v5
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
d_infer'45'complete'45'RBinOp'45'cmp_1792 ::
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
d_infer'45'complete'45'RBinOp'45'cmp_1792 v0 v1 ~v2 v3 v4 v5 v6 v7
                                          v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'cmp_1792
      v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v12
du_infer'45'complete'45'RBinOp'45'cmp_1792 ::
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
du_infer'45'complete'45'RBinOp'45'cmp_1792 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10
  = coe
      du_infer'45'complete'45'RBinOp'45'cmp'8242'_1734 (coe v1)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376 (coe v0)
         (coe v3))
      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v10)
-- Once.TypeCheck.Completeness.Rules.decideLeq-just
d_decideLeq'45'just_1814 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decideLeq'45'just_1814 v0 v1 ~v2
  = du_decideLeq'45'just_1814 v0 v1
du_decideLeq'45'just_1814 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decideLeq'45'just_1814 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.TypeCheck.Completeness.Rules.check-complete-RLam
d_check'45'complete'45'RLam_1846 ::
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
d_check'45'complete'45'RLam_1846 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
                                 ~v10 ~v11 ~v12 v13 ~v14
  = du_check'45'complete'45'RLam_1846 v0 v1 v2 v3 v4 v5 v6 v13
du_check'45'complete'45'RLam_1846 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam_1846 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6392
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
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1306
                                  (coe v5) (coe v4) in
                        coe
                          (let v16 = coe du_decideLeq'45'just_1814 (coe v5) (coe v4) in
                           coe
                             (coe
                                seq (coe v15)
                                (coe
                                   seq (coe v16)
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_withUnit'45'elim_2636
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
d_infer'45'complete'45'RDestruct_1984 ::
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
d_infer'45'complete'45'RDestruct_1984 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                      ~v9 ~v10 ~v11 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                      ~v22 ~v23 ~v24 ~v25
  = du_infer'45'complete'45'RDestruct_1984 v0 v1 v2 v3 v4 v5 v12
du_infer'45'complete'45'RDestruct_1984 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RDestruct_1984 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
                  -> case coe v10 of
                       MAlonzo.Code.Once.Lang.Type.C__'43'__26 v15 v16
                         -> let v17
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
                                      (coe
                                         MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132
                                         (coe v0) (coe v2) (coe v15))
                                      (coe v3) in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v20 v21 v22 v23 v24
                                          -> case coe v21 of
                                               MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v26 v27
                                                 -> let v28
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132
                                                                 (coe v0) (coe v4) (coe v16))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                           -> case coe v29 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v31 v32 v33 v34 v35
                                                                  -> case coe v32 of
                                                                       MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v37 v38
                                                                         -> let v39
                                                                                  = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__214
                                                                                      (coe v6)
                                                                                      (coe v6) in
                                                                            coe
                                                                              (case coe v39 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v40 v41
                                                                                   -> if coe v40
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v41)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_case''_152
                                                                                                     v11
                                                                                                     v27
                                                                                                     v38
                                                                                                     v26
                                                                                                     v37
                                                                                                     v15
                                                                                                     v16
                                                                                                     v12
                                                                                                     v22
                                                                                                     v33)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                           (coe
                                                                                                              v13)
                                                                                                           (coe
                                                                                                              addInt
                                                                                                              (coe
                                                                                                                 (1 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v23)))
                                                                                                        (coe
                                                                                                           addInt
                                                                                                           (coe
                                                                                                              (1 ::
                                                                                                                 Integer))
                                                                                                           (coe
                                                                                                              v34)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           v35)
                                                                                                        erased)))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v41)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
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
d_infer'45'complete'45'RApp'45'generic_2182 ::
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
d_infer'45'complete'45'RApp'45'generic_2182 v0 v1 v2 v3 ~v4 v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RApp'45'generic_2182 v0 v1 v2 v3 v5
du_infer'45'complete'45'RApp'45'generic_2182 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'generic_2182 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6392
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
d_viewBridge_2194 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_AppHeadView_298 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_2194 = erased
-- Once.TypeCheck.Completeness.Rules.otherBridge
d_otherBridge_2206 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Lang.Typing.Scope.T_PolyBuiltinApp_264 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_otherBridge_2206 = erased
-- Once.TypeCheck.Completeness.Rules.infer-complete-RApp-eff
d_infer'45'complete'45'RApp'45'eff_2310 ::
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
d_infer'45'complete'45'RApp'45'eff_2310 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'eff_2310 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'eff_2310 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'eff_2310 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6392
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
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'eff_52) v9
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
d_infer'45'complete'45'RApp'45'act_2408 ::
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
d_infer'45'complete'45'RApp'45'act_2408 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'act_2408 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'act_2408 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'act_2408 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6376
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6392
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
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eg'45'act_50) v9
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
