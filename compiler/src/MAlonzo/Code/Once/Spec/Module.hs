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

module MAlonzo.Code.Once.Spec.Module where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Judgment

-- Once.Spec.Module.AllFunsTyped
d_AllFunsTyped_10 a0 a1 a2 a3 = ()
data T_AllFunsTyped_10
  = C_tnil_18 |
    C_tcons_30 MAlonzo.Code.Once.Type.T_Type_108
               MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
               T_AllFunsTyped_10
-- Once.Spec.Module.ModuleTyped-ef
d_ModuleTyped'45'ef_32 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_ModuleTyped'45'ef_32 = erased
-- Once.Spec.Module.ModuleTyped
d_ModuleTyped_42 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> ()
d_ModuleTyped_42 = erased
-- Once.Spec.Module.EffUU
d_EffUU_46 :: MAlonzo.Code.Once.Type.T_Type_108
d_EffUU_46
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
-- Once.Spec.Module.AllMainEffUU
d_AllMainEffUU_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_AllFunsTyped_10 -> ()
d_AllMainEffUU_56 = erased
-- Once.Spec.Module.MainExists
d_MainExists_72 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_AllFunsTyped_10 -> ()
d_MainExists_72 = erased
-- Once.Spec.Module.ModuleMainEffUU-ef
d_ModuleMainEffUU'45'ef_84 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> ()
d_ModuleMainEffUU'45'ef_84 = erased
-- Once.Spec.Module.ModuleMainExists-ef
d_ModuleMainExists'45'ef_94 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> ()
d_ModuleMainExists'45'ef_94 = erased
-- Once.Spec.Module.HasValidMain-decl
d_HasValidMain'45'decl_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> AgdaAny -> ()
d_HasValidMain'45'decl_102 = erased
