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
-- Once.Parser.TypeAlias.expandAliasesF
d_expandAliasesF_46 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36
d_expandAliasesF_46 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_40 v2
        -> coe
             MAlonzo.Code.Once.Type.C_K_40
             (coe d_expandAliases_48 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8853'__44
             (coe d_expandAliasesF_46 (coe v0) (coe v2))
             (coe d_expandAliasesF_46 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'8855'__46
             (coe d_expandAliasesF_46 (coe v0) (coe v2))
             (coe d_expandAliasesF_46 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.TypeAlias.expandAliases
d_expandAliases_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38
d_expandAliases_48 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_48 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_50 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__52
             (coe d_expandAliases_48 (coe v0) (coe v2))
             (coe d_expandAliases_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__54
             (coe d_expandAliases_48 (coe v0) (coe v2))
             (coe d_expandAliases_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56
             (coe d_expandAliases_48 (coe v0) (coe v2)) (coe v3)
             (coe d_expandAliases_48 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_58
             (coe d_expandAliases_48 (coe v0) (coe v2))
             (coe d_expandAliases_48 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
        -> coe
             MAlonzo.Code.Once.Type.C_μ'45'type_60
             (coe d_expandAliasesF_46 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
        -> coe
             MAlonzo.Code.Once.Type.C_ν'45'type_62
             (coe d_expandAliasesF_46 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Int_64 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_66 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_68 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_70 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
