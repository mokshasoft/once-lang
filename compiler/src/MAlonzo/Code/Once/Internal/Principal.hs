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

module MAlonzo.Code.Once.Internal.Principal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Principal.gradesBelow
d_gradesBelow_6 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  [MAlonzo.Code.Once.Spec.Grade.T_Purity_40]
d_gradesBelow_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Spec.Grade.C_fin_42
                       (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.finBelow
d_finBelow_8 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  [MAlonzo.Code.Once.Spec.Grade.T_Finite_34]
d_finBelow_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.below
d_below_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8]
d_below_12 ~v0 v1 = du_below_12 v1
du_below_12 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8]
du_below_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22)
                   (coe du_below_12 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe du_below_12 (coe v1)))
                   (coe du_below_12 (coe v2))))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24)
                   (coe du_below_12 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe du_below_12 (coe v1)))
                   (coe du_below_12 (coe v2))))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                                     (coe v6))))
                          (coe d_gradesBelow_6 (coe v5))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v4)
                                     (coe v6))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                             (coe d_gradesBelow_6 (coe v5)))
                          (coe du_below_12 (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Spec.Type.C_ν_30 (coe v1))
                (coe d_finBelow_8 (coe v2)))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.PrincipalAt
d_PrincipalAt_50 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_30 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_PrincipalAt_50 = erased
-- Once.Internal.Principal.grade-at-or-below
d_grade'45'at'45'or'45'below_66 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_grade'45'at'45'or'45'below_66 ~v0 ~v1 v2
  = du_grade'45'at'45'or'45'below_66 v2
du_grade'45'at'45'or'45'below_66 ::
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_grade'45'at'45'or'45'below_66 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pure_52
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pa_54
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'pe_56
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'act_58
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'ae_60
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
      MAlonzo.Code.Once.Spec.Grade.C_'8849''45'eff_62
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.fin-at-or-below
d_fin'45'at'45'or'45'below_72 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fin'45'at'45'or'45'below_72 v0 v1 ~v2
  = du_fin'45'at'45'or'45'below_72 v0 v1
du_fin'45'at'45'or'45'below_72 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_fin'45'at'45'or'45'below_72 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.pair-below
d_pair'45'below_94 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pair'45'below_94 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_pair'45'below_94 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_pair'45'below_94 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_pair'45'below_94 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
        -> case coe v8 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
                          (coe v5)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v5))
                          (coe v6))
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProductWith'8314'_342
                          v0
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v5))
                          v6 v1 v3
                          (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                          v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> case coe v8 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
                          (coe v5)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProductWith'8314'_342
                          v0 v5
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          v1 v3 v9
                          (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
                          (coe v5)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v5))
                          (coe v6))
                       (coe
                          MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'cartesianProductWith'8314'_342
                          v0
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v5))
                          v6 v1 v3
                          (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9) v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.void-below
d_void'45'below_134 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_void'45'below_134 ~v0 v1 = du_void'45'below_134 v1
du_void'45'below_134 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_void'45'below_134 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.tail
d_tail_164 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_tail_164 ~v0 ~v1 ~v2 ~v3 v4 = du_tail_164 v4
du_tail_164 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_tail_164 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.at-or-below-<:ᶜ
d_at'45'or'45'below'45''60''58''7580'_176 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at'45'or'45'below'45''60''58''7580'_176 ~v0 v1 v2 v3
  = du_at'45'or'45'below'45''60''58''7580'_176 v1 v2 v3
du_at'45'or'45'below'45''60''58''7580'_176 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_at'45'or'45'below'45''60''58''7580'_176 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'void_82
        -> coe du_void'45'below_134 (coe v0)
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'var_86
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'unit_88
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'int_90
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'float_92
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'arr_106 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                      -> case coe v1 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                                    -> coe
                                         du_tail_164
                                         (coe
                                            du_pair'45'below_94
                                            (coe
                                               (\ v21 ->
                                                  coe
                                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                    (coe v16)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                       (coe v19) (coe v21))))
                                            (coe v20) (coe v15) (coe v18) (coe v13)
                                            (coe d_gradesBelow_6 (coe v15))
                                            (coe du_below_12 (coe v13))
                                            (coe du_grade'45'at'45'or'45'below_66 (coe v10))
                                            (coe
                                               du_at'45'or'45'below'45''60''58''7580'_176 (coe v13)
                                               (coe v18) (coe v9)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''42'_116 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__22 v11 v12
                      -> coe
                           du_tail_164
                           (coe
                              du_pair'45'below_94 (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22)
                              (coe v11) (coe v9) (coe v12) (coe v10) (coe du_below_12 (coe v9))
                              (coe du_below_12 (coe v10))
                              (coe
                                 du_at'45'or'45'below'45''60''58''7580'_176 (coe v9) (coe v11)
                                 (coe v7))
                              (coe
                                 du_at'45'or'45'below'45''60''58''7580'_176 (coe v10) (coe v12)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45''43'_126 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                      -> coe
                           du_tail_164
                           (coe
                              du_pair'45'below_94 (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24)
                              (coe v11) (coe v9) (coe v12) (coe v10) (coe du_below_12 (coe v9))
                              (coe du_below_12 (coe v10))
                              (coe
                                 du_at'45'or'45'below'45''60''58''7580'_176 (coe v9) (coe v11)
                                 (coe v7))
                              (coe
                                 du_at'45'or'45'below'45''60''58''7580'_176 (coe v10) (coe v12)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'μ_130
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Spec.Sub.C_sub'7580''45'ν_138 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v9 v10
                      -> coe
                           du_ν'45'step_212 (coe v10) (coe v8)
                           (coe du_fin'45'at'45'or'45'below_72 (coe v10) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal._.ν-step
d_ν'45'step_212 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ν'45'step_212 ~v0 ~v1 v2 v3 ~v4 v5 = du_ν'45'step_212 v2 v3 v5
du_ν'45'step_212 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_ν'45'step_212 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                (coe
                   MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'map'8314'_164
                   v0 (d_finBelow_8 (coe v1)) v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Principal.below-complete
d_below'45'complete_222 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_below'45'complete_222 ~v0 v1 v2 v3 ~v4
  = du_below'45'complete_222 v1 v2 v3
du_below'45'complete_222 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_below'45'complete_222 v0 v1 v2
  = coe
      du_strict_236
      (coe
         du_at'45'or'45'below'45''60''58''7580'_176 (coe v0) (coe v1)
         (coe v2))
-- Once.Internal.Principal._.strict
d_strict_236 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58''7580'__76 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_strict_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 = du_strict_236 v7
du_strict_236 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_strict_236 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
