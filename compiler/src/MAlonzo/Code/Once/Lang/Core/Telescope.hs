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

module MAlonzo.Code.Once.Lang.Core.Telescope where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.Meaning
import qualified MAlonzo.Code.Once.Lang.Core.PolySub
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.PolyTyping
import qualified MAlonzo.Code.Once.Lang.GradedOps
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Lang.Core.Telescope.Tele
d_Tele_12 a0 a1 a2 = ()
data T_Tele_12
  = C_'91''93'_16 |
    C_def_28 T_Tele_12 MAlonzo.Code.Once.Lang.Core.PolyTyping.T_PTm_402
             MAlonzo.Code.Once.Lang.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
-- Once.Lang.Core.Telescope.teleSem
d_teleSem_36 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  T_Tele_12 -> MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_360
d_teleSem_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Meaning.C_defSem_378
      (coe
         d_teleDefs_50 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe v4)
-- Once.Lang.Core.Telescope.teleDefs
d_teleDefs_50 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  AgdaAny
d_teleDefs_50 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      C_def_28 v12 v14 v15
        -> let v16 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v18 v19
                  -> case coe v6 of
                       MAlonzo.Code.Data.Fin.Base.C_zero_12
                         -> coe
                              MAlonzo.Code.Once.Lang.Core.Meaning.du_'10214'_'10215'_502 v0
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.PolyTyping.du__'10218'_'10219''7580'_458
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848
                                       (coe
                                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe MAlonzo.Code.Once.Lang.Core.PolyTyping.C_'8709'_366) (coe v7))
                              (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.PolyTyping.du__'10218'_'10219''8348'_504
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848
                                       (coe
                                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe v14) (coe v7))
                              (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848
                                       (coe
                                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe MAlonzo.Code.Once.Lang.Core.PolyTy.d_type_820 (coe v19))
                                 (coe v7))
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.PolyTyping.du_instantiate_1090
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.PolyTy.d_arity_816
                                    (coe
                                       MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848
                                       (coe
                                          MAlonzo.Code.Once.Lang.Core.PolyTy.C__'9655'__834 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe v14)
                                 (coe MAlonzo.Code.Once.Lang.Core.PolyTy.d_type_820 (coe v19))
                                 (coe v7) (coe v8) (coe v15))
                              v3
                              (d_teleSem_36
                                 (coe v0) (coe v16) (coe v18) (coe v3) (coe v4) (coe v12))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Data.Fin.Base.C_suc_16 v21
                         -> coe
                              d_teleDefs_50 (coe v0) (coe v16) (coe v18) (coe v3) (coe v4)
                              (coe v12) (coe v21) (coe v7) (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.IOUnit
d_IOUnit_92 :: MAlonzo.Code.Once.Lang.Core.PolyTy.T_Ty_16
d_IOUnit_92
  = coe
      MAlonzo.Code.Once.Lang.Core.PolyTy.C__'8658''91'_'93'__38
      (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26)
      (coe
         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38))
      (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_Unit_26)
-- Once.Lang.Core.Telescope.noVars
d_noVars_94 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_noVars_94 ~v0 = du_noVars_94
du_noVars_94 :: MAlonzo.Code.Once.Lang.Type.T_Type_8
du_noVars_94 = MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.noKinds
d_noKinds_96 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_TKind_10
d_noKinds_96 ~v0 = du_noKinds_96
du_noKinds_96 :: MAlonzo.Code.Once.Lang.Type.T_TKind_10
du_noKinds_96 = MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.MainEntry
d_MainEntry_98 a0 = ()
newtype T_MainEntry_98
  = C_entry_102 MAlonzo.Code.Once.Lang.Core.PolySub.T__'60''58''8346'__10
-- Once.Lang.Core.Telescope.Program
d_Program_106 a0 = ()
data T_Program_106
  = C_program_130 Integer
                  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 T_Tele_12
                  MAlonzo.Code.Data.Fin.Base.T_Fin_10 T_MainEntry_98
-- Once.Lang.Core.Telescope.Program.size
d_size_120 :: T_Program_106 -> Integer
d_size_120 v0
  = case coe v0 of
      C_program_130 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.Program.sig
d_sig_122 ::
  T_Program_106 -> MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826
d_sig_122 v0
  = case coe v0 of
      C_program_130 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.Program.defs
d_defs_124 :: T_Program_106 -> T_Tele_12
d_defs_124 v0
  = case coe v0 of
      C_program_130 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.Program.main
d_main_126 :: T_Program_106 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_main_126 v0
  = case coe v0 of
      C_program_130 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.Program.isMain
d_isMain_128 :: T_Program_106 -> T_MainEntry_98
d_isMain_128 v0
  = case coe v0 of
      C_program_130 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.EntrySem
d_EntrySem_132 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 -> ()
d_EntrySem_132 = erased
-- Once.Lang.Core.Telescope.noResp
d_noResp_138 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
d_noResp_138 ~v0 = du_noResp_138
du_noResp_138 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8
du_noResp_138 = MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.runEntry
d_runEntry_142 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Schema_808 ->
  T_MainEntry_98 ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
   (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
   AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_runEntry_142 v0 v1 v2
  = case coe v1 of
      C_entry_102 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Core.PolyTy.C_schema_822 v5 v6 v7
               -> coe
                    MAlonzo.Code.Once.Lang.GradedOps.d_'10214'_'10215''60''58''7515'_492
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe (0 :: Integer)) (coe v7) (\ v8 -> coe du_noVars_94))
                    (MAlonzo.Code.Once.Lang.Core.PolyTy.d__'10218'_'10219'_344
                       (coe (0 :: Integer)) (coe d_IOUnit_92) (\ v8 -> coe du_noVars_94))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.PolySub.du_'60''58''8346''45''10218''10219'_90
                       (coe v7) (coe d_IOUnit_92) (\ v8 -> coe du_noVars_94) (coe v4))
                    (coe v2 (\ v8 -> coe du_noVars_94) (\ v8 -> coe du_noResp_138))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Telescope.runCore
d_runCore_150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Program_106 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_58
d_runCore_150 v0 v1 v2 v3
  = case coe v2 of
      C_program_130 v4 v5 v6 v7 v8
        -> coe
             d_runEntry_142
             (coe
                MAlonzo.Code.Once.Lang.Core.PolyTy.du__'33''33'__848 (coe v5)
                (coe v7))
             (coe v8)
             (coe
                MAlonzo.Code.Once.Lang.Core.Meaning.d_defs_374
                (d_teleSem_36
                   (coe v0) (coe v4) (coe v5) (coe v1) (coe v3) (coe v6))
                v7)
      _ -> MAlonzo.RTE.mazUnreachableError
