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

module MAlonzo.Code.Once.Parser.TypeAlias where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.TypeAlias.TypeAlias
d_TypeAlias_6 :: ()
d_TypeAlias_6 = erased
-- Once.Parser.TypeAlias.TypeAliasEnv
d_TypeAliasEnv_8 :: ()
d_TypeAliasEnv_8 = erased
-- Once.Parser.TypeAlias.lookupAlias
d_lookupAlias_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupAlias_10 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v0))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                  (coe v4)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                                 else coe seq (coe v8) (coe d_lookupAlias_10 (coe v0) (coe v3))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.substTVarF
d_substTVarF_46 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  MAlonzo.Code.Once.Type.T_Functor_32
d_substTVarF_46 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_K_36 v3
        -> coe
             MAlonzo.Code.Once.Type.C_K_36
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Type.C_Id_38 -> coe v2
      MAlonzo.Code.Once.Type.C__'8853'__40 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8853'__40
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v3))
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C__'8855'__42 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8855'__42
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v3))
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.substTVar
d_substTVar_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34
d_substTVar_48 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_Unit_44 -> coe v2
      MAlonzo.Code.Once.Type.C_Void_46 -> coe v2
      MAlonzo.Code.Once.Type.C__'42'__48 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__48
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v3))
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C__'43'__50 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__50
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v3))
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v3)) (coe v4)
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.Type.C_Eff_54 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_54
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v3))
             (coe d_substTVar_48 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.Type.C_μ'45'type_56 v3
        -> coe
             MAlonzo.Code.Once.Type.C_μ'45'type_56
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Type.C_ν'45'type_58 v3
        -> coe
             MAlonzo.Code.Once.Type.C_ν'45'type_58
             (coe d_substTVarF_46 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Type.C_Int_60 -> coe v2
      MAlonzo.Code.Once.Type.C_Float_62 -> coe v2
      MAlonzo.Code.Once.Type.C_Str_64 -> coe v2
      MAlonzo.Code.Once.Type.C_Buffer_66 -> coe v2
      MAlonzo.Code.Once.Type.C_TVar_68 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v1)
                       else coe seq (coe v6) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.applySubsts
d_applySubsts_140 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34
d_applySubsts_140 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    d_applySubsts_140 (coe v3)
                    (coe d_substTVar_48 (coe v4) (coe v5) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.expandAliasesF
d_expandAliasesF_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Functor_32 ->
  MAlonzo.Code.Once.Type.T_Functor_32
d_expandAliasesF_152 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_36 v2
        -> coe
             MAlonzo.Code.Once.Type.C_K_36
             (coe d_expandAliases_154 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Id_38 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__40 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8853'__40
             (coe d_expandAliasesF_152 (coe v0) (coe v2))
             (coe d_expandAliasesF_152 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8855'__42 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8855'__42
             (coe d_expandAliasesF_152 (coe v0) (coe v2))
             (coe d_expandAliasesF_152 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.expandAliases
d_expandAliases_154 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34
d_expandAliases_154 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_44 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_46 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__48 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__48
             (coe d_expandAliases_154 (coe v0) (coe v2))
             (coe d_expandAliases_154 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__50 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__50
             (coe d_expandAliases_154 (coe v0) (coe v2))
             (coe d_expandAliases_154 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52
             (coe d_expandAliases_154 (coe v0) (coe v2)) (coe v3)
             (coe d_expandAliases_154 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_54 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_54
             (coe d_expandAliases_154 (coe v0) (coe v2))
             (coe d_expandAliases_154 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_μ'45'type_56 v2
        -> coe
             MAlonzo.Code.Once.Type.C_μ'45'type_56
             (coe d_expandAliasesF_152 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_ν'45'type_58 v2
        -> coe
             MAlonzo.Code.Once.Type.C_ν'45'type_58
             (coe d_expandAliasesF_152 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Int_60 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_62 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_64 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_66 -> coe v1
      MAlonzo.Code.Once.Type.C_TVar_68 v2
        -> let v3 = d_lookupAlias_10 (coe v2) (coe v0) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              [] -> coe d_expandAliases_154 (coe v0) (coe v6)
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
