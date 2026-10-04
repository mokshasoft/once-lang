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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment

-- Once.Spec.Module.Scope
d_Scope_6 = ()
data T_Scope_6
  = C_scope_16 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
               [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116]
-- Once.Spec.Module.Scope.imps
d_imps_12 :: T_Scope_6 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imps_12 v0
  = case coe v0 of
      C_scope_16 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Module.Scope.tele
d_tele_14 ::
  T_Scope_6 -> [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116]
d_tele_14 v0
  = case coe v0 of
      C_scope_16 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Module.emptyScope
d_emptyScope_18 :: T_Scope_6
d_emptyScope_18
  = coe
      C_scope_16 (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_46)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Spec.Module.ctxOf
d_ctxOf_20 ::
  T_Scope_6 -> MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctxOf_20 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
      (coe d_imps_12 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_buildPolyCtx_272
         (coe d_tele_14 (coe v0)))
-- Once.Spec.Module.addImp
d_addImp_24 ::
  T_Scope_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_Scope_6
d_addImp_24 v0 v1 v2
  = coe
      C_scope_16
      (coe
         MAlonzo.Code.Once.Compile.d_extendFunCtx_48
         (coe d_imps_12 (coe v0)) (coe v1) (coe v2))
      (coe d_tele_14 (coe v0))
-- Once.Spec.Module.addPoly
d_addPoly_32 ::
  T_Scope_6 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 -> T_Scope_6
d_addPoly_32 v0 v1
  = coe
      C_scope_16 (coe d_imps_12 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe d_tele_14 (coe v0)))
-- Once.Spec.Module.ModTele
d_ModTele_38 a0 a1 = ()
data T_ModTele_38
  = C_'91''93'_42 |
    C_ffi_52 MAlonzo.Code.Once.Type.T_Type_108
             MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 AgdaAny
             MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 T_ModTele_38 |
    C_mono_64 MAlonzo.Code.Once.Type.T_Type_108
              MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
              MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
              T_ModTele_38 |
    C_poly_74 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
              T_ModTele_38
-- Once.Spec.Module.entrySig-fun
d_entrySig'45'fun_76 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  Bool ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_entrySig'45'fun_76 v0 v1 v2 v3
  = if coe v1
      then case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v0)) (coe v4))
                    (coe v3)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      else coe v3
-- Once.Spec.Module.entrySig
d_entrySig_92 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_entrySig_92 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v3
               -> coe
                    d_entrySig'45'fun_76 (coe v3)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v3))
                    (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
                    (coe d_entrySig_92 (coe v2))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v3
               -> coe d_entrySig_92 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Module.teleSig
d_teleSig_104 ::
  T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_ModTele_38 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_teleSig_104 ~v0 v1 v2 = du_teleSig_104 v1 v2
du_teleSig_104 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_ModTele_38 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_teleSig_104 v0 v1
  = case coe v1 of
      C_'91''93'_42 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C_ffi_52 v4 v8 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v14)) (coe v4))
                           (coe du_teleSig_104 (coe v13) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_mono_64 v4 v6 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13 -> coe du_teleSig_104 (coe v13) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_74 v5 v6 v7
        -> case coe v0 of
             (:) v8 v9 -> coe du_teleSig_104 (coe v9) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Module.teleSig≡entrySig
d_teleSig'8801'entrySig_122 ::
  T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  T_ModTele_38 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_teleSig'8801'entrySig_122 = erased
-- Once.Spec.Module.moduleSig-ef
d_moduleSig'45'ef_156 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_moduleSig'45'ef_156 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_entrySig_92 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Module.moduleSig
d_moduleSig_160 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_moduleSig_160 v0
  = coe
      d_moduleSig'45'ef_156
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
         (coe v0))
-- Once.Spec.Module.ModuleTyped-ef
d_ModuleTyped'45'ef_164 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_ModuleTyped'45'ef_164 = erased
-- Once.Spec.Module.ModuleTyped
d_ModuleTyped_172 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> ()
d_ModuleTyped_172 = erased
-- Once.Spec.Module.EffUU
d_EffUU_176 :: MAlonzo.Code.Once.Type.T_Type_108
d_EffUU_176
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
-- Once.Spec.Module.MainsEffUU
d_MainsEffUU_182 ::
  T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_ModTele_38 -> ()
d_MainsEffUU_182 = erased
-- Once.Spec.Module.MainIn
d_MainIn_198 ::
  T_Scope_6 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_ModTele_38 -> ()
d_MainIn_198 = erased
-- Once.Spec.Module.HasValidMain-ef
d_HasValidMain'45'ef_214 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> ()
d_HasValidMain'45'ef_214 = erased
-- Once.Spec.Module.HasValidMain
d_HasValidMain_222 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny -> ()
d_HasValidMain_222 = erased
