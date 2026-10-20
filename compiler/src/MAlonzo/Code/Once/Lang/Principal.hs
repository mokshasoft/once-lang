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

module MAlonzo.Code.Once.Lang.Principal where

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
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Typing.Scope

-- Once.Lang.Principal.gradesBelow
d_gradesBelow_6 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  [MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32]
d_gradesBelow_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.finBelow
d_finBelow_8 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  [MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40]
d_finBelow_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.below
d_below_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Lang.Type.T_Type_8]
d_below_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24)
                   (coe d_below_10 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe d_below_10 (coe v1)))
                   (coe d_below_10 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26)
                   (coe d_below_10 (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe d_below_10 (coe v1)))
                   (coe d_below_10 (coe v2))))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70
                          (coe
                             (\ v6 ->
                                coe
                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v4)
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
                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v4)
                                     (coe v6))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                             (coe d_gradesBelow_6 (coe v5)))
                          (coe d_below_10 (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v1))
                (coe d_finBelow_8 (coe v2)))
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.PrincipalAt
d_PrincipalAt_48 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_PrincipalAt_48 = erased
-- Once.Lang.Principal.grade-at-or-below
d_grade'45'at'45'or'45'below_64 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_grade'45'at'45'or'45'below_64 ~v0 ~v1 v2
  = du_grade'45'at'45'or'45'below_64 v2
du_grade'45'at'45'or'45'below_64 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_grade'45'at'45'or'45'below_64 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'eff_12
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pe_14
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'act_16
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pa_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'ae_20
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.fin-at-or-below
d_fin'45'at'45'or'45'below_70 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fin'45'at'45'or'45'below_70 v0 v1 ~v2
  = du_fin'45'at'45'or'45'below_70 v0 v1
du_fin'45'at'45'or'45'below_70 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_fin'45'at'45'or'45'below_70 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Grade.C_act_44
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.pair-below
d_pair'45'below_92 ::
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
d_pair'45'below_92 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_pair'45'below_92 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_pair'45'below_92 ::
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
du_pair'45'below_92 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
-- Once.Lang.Principal.void-below
d_void'45'below_130 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_void'45'below_130 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.tail
d_tail_160 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Lang.Type.T_Type_8] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_tail_160 ~v0 ~v1 ~v2 v3 = du_tail_160 v3
du_tail_160 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_tail_160 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal.at-or-below-<:ᶜ
d_at'45'or'45'below'45''60''58''7580'_170 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_at'45'or'45'below'45''60''58''7580'_170 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'void_126
        -> coe d_void'45'below_130 (coe v1)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'unit_128
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'int_130
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'float_132
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'arr_146 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v14 v15
                      -> case coe v1 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v19 v20
                                    -> coe
                                         du_tail_160
                                         (coe
                                            du_pair'45'below_92
                                            (coe
                                               (\ v21 ->
                                                  coe
                                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                    (coe v11)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                       (coe v14) (coe v21))))
                                            (coe v15) (coe v20) (coe v13) (coe v18)
                                            (coe d_gradesBelow_6 (coe v20))
                                            (coe d_below_10 (coe v18))
                                            (coe du_grade'45'at'45'or'45'below_64 (coe v10))
                                            (coe
                                               d_at'45'or'45'below'45''60''58''7580'_170 (coe v13)
                                               (coe v18) (coe v9)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'prod_156 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v11 v12
                      -> coe
                           du_tail_160
                           (coe
                              du_pair'45'below_92 (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24)
                              (coe v9) (coe v11) (coe v10) (coe v12) (coe d_below_10 (coe v11))
                              (coe d_below_10 (coe v12))
                              (coe
                                 d_at'45'or'45'below'45''60''58''7580'_170 (coe v9) (coe v11)
                                 (coe v7))
                              (coe
                                 d_at'45'or'45'below'45''60''58''7580'_170 (coe v10) (coe v12)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'sum_166 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
                      -> coe
                           du_tail_160
                           (coe
                              du_pair'45'below_92 (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26)
                              (coe v9) (coe v11) (coe v10) (coe v12) (coe d_below_10 (coe v11))
                              (coe d_below_10 (coe v12))
                              (coe
                                 d_at'45'or'45'below'45''60''58''7580'_170 (coe v9) (coe v11)
                                 (coe v7))
                              (coe
                                 d_at'45'or'45'below'45''60''58''7580'_170 (coe v10) (coe v12)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'μ_170
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'ν_178 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v9 v10
                      -> coe
                           du_ν'45'step_206 (coe v8) (coe v10)
                           (coe du_fin'45'at'45'or'45'below_70 (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'7580''45'rigid_184
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Principal._.ν-step
d_ν'45'step_206 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ν'45'step_206 ~v0 v1 v2 ~v3 v4 = du_ν'45'step_206 v1 v2 v4
du_ν'45'step_206 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_ν'45'step_206 v0 v1 v2
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
-- Once.Lang.Principal.below-complete
d_below'45'complete_214 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_below'45'complete_214 v0 v1 v2 ~v3
  = du_below'45'complete_214 v0 v1 v2
du_below'45'complete_214 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_below'45'complete_214 v0 v1 v2
  = coe
      du_strict_228
      (coe
         d_at'45'or'45'below'45''60''58''7580'_170 (coe v0) (coe v1)
         (coe v2))
-- Once.Lang.Principal._.strict
d_strict_228 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58''7580'__122 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_strict_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 = du_strict_228 v6
du_strict_228 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_strict_228 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
