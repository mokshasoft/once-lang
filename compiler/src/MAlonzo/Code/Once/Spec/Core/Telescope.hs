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

module MAlonzo.Code.Once.Spec.Core.Telescope where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Core.Telescope.Tele
d_Tele_12 a0 a1 a2 = ()
data T_Tele_12
  = C_'91''93'_16 |
    C_def_28 T_Tele_12 MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390
             MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730
-- Once.Spec.Core.Telescope.teleSem
d_teleSem_36 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  T_Tele_12 -> MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348
d_teleSem_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Spec.Core.Meaning.C_defSem_366
      (coe
         d_teleDefs_50 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe v4)
-- Once.Spec.Core.Telescope.teleDefs
d_teleDefs_50 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  T_Tele_12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  AgdaAny
d_teleDefs_50 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      C_def_28 v12 v14 v15
        -> let v16 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v18 v19
                  -> case coe v6 of
                       MAlonzo.Code.Data.Fin.Base.C_zero_12
                         -> coe
                              MAlonzo.Code.Once.Spec.Core.Meaning.du_'10214'_'10215'_460 v0
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTyping.du__'10218'_'10219''7580'_444
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
                                    (coe
                                       MAlonzo.Code.Once.Spec.Core.PolyTy.du__'33''33'__886
                                       (coe
                                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe MAlonzo.Code.Once.Spec.Core.PolyTyping.C_'8709'_354) (coe v7))
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTyping.du__'10218'_'10219''8348'_490
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
                                    (coe
                                       MAlonzo.Code.Once.Spec.Core.PolyTy.du__'33''33'__886
                                       (coe
                                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe v14) (coe v7))
                              (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_382
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
                                    (coe
                                       MAlonzo.Code.Once.Spec.Core.PolyTy.du__'33''33'__886
                                       (coe
                                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe MAlonzo.Code.Once.Spec.Core.PolyTy.d_type_858 (coe v19))
                                 (coe v7))
                              (coe MAlonzo.Code.Once.Type.C_pure_34)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.PolyTyping.du_instantiate_1148
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.PolyTy.d_arity_854
                                    (coe
                                       MAlonzo.Code.Once.Spec.Core.PolyTy.du__'33''33'__886
                                       (coe
                                          MAlonzo.Code.Once.Spec.Core.PolyTy.C__'9655'__872 v18 v19)
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe v14)
                                 (coe MAlonzo.Code.Once.Spec.Core.PolyTy.d_type_858 (coe v19))
                                 (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v7) (coe v8) (coe v15))
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
-- Once.Spec.Core.Telescope.IOUnit
d_IOUnit_92 :: MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16
d_IOUnit_92
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.C__'8658''91'_'93'__38
      (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_Unit_26)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Spec.Core.PolyTy.C_Unit_26)
-- Once.Spec.Core.Telescope.noVars
d_noVars_94 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_noVars_94 ~v0 = du_noVars_94
du_noVars_94 :: MAlonzo.Code.Once.Type.T_Type_108
du_noVars_94 = MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.noKinds
d_noKinds_96 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_TKind_110
d_noKinds_96 ~v0 = du_noKinds_96
du_noKinds_96 :: MAlonzo.Code.Once.Type.T_TKind_110
du_noKinds_96 = MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.Program
d_Program_100 a0 = ()
data T_Program_100
  = C_program_124 Integer
                  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 T_Tele_12
                  MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Once.Spec.Core.Telescope.Program.size
d_size_114 :: T_Program_100 -> Integer
d_size_114 v0
  = case coe v0 of
      C_program_124 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.Program.sig
d_sig_116 ::
  T_Program_100 -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864
d_sig_116 v0
  = case coe v0 of
      C_program_124 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.Program.defs
d_defs_118 :: T_Program_100 -> T_Tele_12
d_defs_118 v0
  = case coe v0 of
      C_program_124 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.Program.main
d_main_120 :: T_Program_100 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_main_120 v0
  = case coe v0 of
      C_program_124 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.Program.mainTy
d_mainTy_122 ::
  T_Program_100 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mainTy_122 = erased
-- Once.Spec.Core.Telescope.EntrySem
d_EntrySem_126 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 -> ()
d_EntrySem_126 = erased
-- Once.Spec.Core.Telescope.noResp
d_noResp_132 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_noResp_132 ~v0 = du_noResp_132
du_noResp_132 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
du_noResp_132 = MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Telescope.runEntry
d_runEntry_136 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Once.Type.T_Type_108) ->
   (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
   AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_runEntry_136 ~v0 ~v1 v2 = du_runEntry_136 v2
du_runEntry_136 ::
  ((MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Once.Type.T_Type_108) ->
   (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
   AgdaAny) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_runEntry_136 v0
  = coe
      v0 (\ v1 -> coe du_noVars_94) (\ v1 -> coe du_noResp_132)
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Spec.Core.Telescope.runProgram
d_runProgram_146 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_Program_100 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_runProgram_146 v0 v1 v2 v3 v4
  = case coe v2 of
      C_program_124 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_542
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_278 (coe v0)
                (coe v3))
             (coe
                du_runEntry_136
                (coe
                   MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_362
                   (d_teleSem_36
                      (coe v0) (coe v5) (coe v6) (coe v1) (coe v3) (coe v7))
                   v8))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
