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

module MAlonzo.Code.Once.Optimize where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize.PairView
d_PairView_10 a0 a1 a2 a3 = ()
data T_PairView_10 = C_is'45'pair_22 | C_is'45'other'45'pair_32
-- Once.Optimize.CoprodView
d_CoprodView_40 a0 a1 a2 a3 = ()
data T_CoprodView_40
  = C_is'45'inl_46 | C_is'45'inr_52 | C_is'45'other'45'coprod_62
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_68 a0 a1 a2 = ()
data T_ComposeFirstView_68
  = C_cf'45'id_72 | C_cf'45'terminal_76 | C_cf'45'fst_82 |
    C_cf'45'snd_88 | C_cf'45'case_100 | C_cf'45'comp_112 |
    C_cf'45'other_120
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_126 a0 a1 a2 = ()
data T_ComposeSecondView_126
  = C_cs'45'id_130 | C_cs'45'initial_134 | C_cs'45'other_142
-- Once.Optimize.FstSndView
d_FstSndView_148 a0 a1 a2 = ()
data T_FstSndView_148
  = C_fsv'45'fst_154 | C_fsv'45'snd_160 | C_fsv'45'other_168
-- Once.Optimize.InlInrView
d_InlInrView_174 a0 a1 a2 = ()
data T_InlInrView_174
  = C_iiv'45'inl_180 | C_iiv'45'inr_186 | C_iiv'45'other_194
-- Once.Optimize.pairView-gen
d_pairView'45'gen_208 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_10
d_pairView'45'gen_208 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_208 v2
du_pairView'45'gen_208 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
du_pairView'45'gen_208 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_22
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'pair_32
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_is'45'other'45'pair_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_300 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
d_pairView_300 ~v0 ~v1 ~v2 v3 = du_pairView_300 v3
du_pairView_300 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
du_pairView_300 v0 = coe du_pairView'45'gen_208 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_316 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CoprodView_40
d_coprodView'45'gen_316 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_316 v2
du_coprodView'45'gen_316 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
du_coprodView'45'gen_316 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_46
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_52
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_curry_84 v4
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_Iter_130 v4
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'coprod_62
      MAlonzo.Code.Once.IR.C_Call_146 v3
        -> coe C_is'45'other'45'coprod_62
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_406 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
d_coprodView_406 ~v0 ~v1 ~v2 v3 = du_coprodView_406 v3
du_coprodView_406 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
du_coprodView_406 v0 = coe du_coprodView'45'gen_316 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_416 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_68
d_composeFirstView_416 ~v0 ~v1 v2 = du_composeFirstView_416 v2
du_composeFirstView_416 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_68
du_composeFirstView_416 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_72
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_cf'45'comp_112
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_82
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_88
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_100
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_76
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cf'45'other_120
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cf'45'other_120
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_464 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_126
d_composeSecondView_464 ~v0 ~v1 v2 = du_composeSecondView_464 v2
du_composeSecondView_464 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_126
du_composeSecondView_464 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_130
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_134
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cs'45'other_142
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cs'45'other_142
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.ChainView
d_ChainView_510 a0 a1 a2 = ()
data T_ChainView_510 = C_is'45'comp_522 | C_not'45'comp_530
-- Once.Optimize.chainView
d_chainView_538 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_510
d_chainView_538 ~v0 ~v1 v2 = du_chainView_538 v2
du_chainView_538 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_510
du_chainView_538 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_is'45'comp_522
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_not'45'comp_530
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_not'45'comp_530
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_586 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_148
d_fstSndView_586 ~v0 ~v1 v2 = du_fstSndView_586 v2
du_fstSndView_586 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_148
du_fstSndView_586 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_154
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_160
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_fsv'45'other_168
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_fsv'45'other_168
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_634 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_174
d_inlInrView_634 ~v0 ~v1 v2 = du_inlInrView_634 v2
du_inlInrView_634 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_174
du_inlInrView_634 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_180
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_186
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_iiv'45'other_194
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_iiv'45'other_194
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_680 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_680 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_680 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_680 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_680 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_680
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           d_has'45'effect'63'_680
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v1)))
                           (coe v1) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           d_has'45'effect'63'_680 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v9))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_Call_146 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.compose-second-aux
d_compose'45'second'45'aux_710 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_126 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'second'45'aux_710 ~v0 v1 ~v2 v3 v4 v5
  = du_compose'45'second'45'aux_710 v1 v3 v4 v5
du_compose'45'second'45'aux_710 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_126 -> MAlonzo.Code.Once.IR.T_IR_16
du_compose'45'second'45'aux_710 v0 v1 v2 v3
  = case coe v3 of
      C_cs'45'id_130 -> coe v1
      C_cs'45'initial_134 -> coe MAlonzo.Code.Once.IR.C_initial_76
      C_cs'45'other_142
        -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_726 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_726 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_726 v1 v3 v4
du_optimize'45'compose'45'second_726 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_726 v0 v1 v2
  = coe
      du_compose'45'second'45'aux_710 (coe v0) (coe v1) (coe v2)
      (coe du_composeSecondView_464 (coe v2))
-- Once.Optimize.fst-pair
d_fst'45'pair_742 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'pair_742 ~v0 v1 v2 v3 v4 v5
  = du_fst'45'pair_742 v1 v2 v3 v4 v5
du_fst'45'pair_742 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'pair_742 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v2
-- Once.Optimize.fst-chain-pair
d_fst'45'chain'45'pair_766 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'pair_766 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_fst'45'chain'45'pair_766 v1 v2 v3 v4 v5 v6 v7
du_fst'45'chain'45'pair_766 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'pair_766 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v0
                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v3 v4) v5)
      else coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v5
-- Once.Optimize.fst-chain-aux
d_fst'45'chain'45'aux_792 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'aux_792 ~v0 v1 v2 v3 v4 v5 v6
  = du_fst'45'chain'45'aux_792 v1 v2 v3 v4 v5 v6
du_fst'45'chain'45'aux_792 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'aux_792 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_fst'45'chain'45'pair_766 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v2) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-chain
d_fst'45'chain_812 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain_812 ~v0 v1 v2 v3 v4
  = du_fst'45'chain_812 v1 v2 v3 v4
du_fst'45'chain_812 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain_812 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_522
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_fst'45'chain'45'aux_792 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_300 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_530
        -> coe
             du_optimize'45'compose'45'second_726
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-aux
d_fst'45'aux_828 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'aux_828 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_fst'45'pair_742 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v2) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             du_fst'45'chain_812 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_538 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_842 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_842 v0 v1 v2 v3
  = coe
      d_fst'45'aux_828 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_300 (coe v3))
-- Once.Optimize.snd-pair
d_snd'45'pair_856 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'pair_856 ~v0 v1 v2 v3 v4 v5
  = du_snd'45'pair_856 v1 v2 v3 v4 v5
du_snd'45'pair_856 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'pair_856 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v3
-- Once.Optimize.snd-chain-pair
d_snd'45'chain'45'pair_880 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'pair_880 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_snd'45'chain'45'pair_880 v1 v2 v3 v4 v5 v6 v7
du_snd'45'chain'45'pair_880 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'pair_880 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v0
                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v3 v4) v5)
      else coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v4 v5
-- Once.Optimize.snd-chain-aux
d_snd'45'chain'45'aux_906 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'aux_906 ~v0 v1 v2 v3 v4 v5 v6
  = du_snd'45'chain'45'aux_906 v1 v2 v3 v4 v5 v6
du_snd'45'chain'45'aux_906 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'aux_906 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_snd'45'chain'45'pair_880 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v1) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-chain
d_snd'45'chain_926 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain_926 ~v0 v1 v2 v3 v4
  = du_snd'45'chain_926 v1 v2 v3 v4
du_snd'45'chain_926 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain_926 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_522
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_snd'45'chain'45'aux_906 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_300 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_530
        -> coe
             du_optimize'45'compose'45'second_726
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-aux
d_snd'45'aux_942 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'aux_942 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_snd'45'pair_856 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_680 (coe v0) (coe v1) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             du_snd'45'chain_926 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_538 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-snd
d_optimize'45'snd_956 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_956 v0 v1 v2 v3
  = coe
      d_snd'45'aux_942 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_300 (coe v3))
-- Once.Optimize.post-case-chain-aux
d_post'45'case'45'chain'45'aux_978 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'chain'45'aux_978 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_post'45'case'45'chain'45'aux_978 v0 v1 v4 v5 v6 v7 v8 v9
du_post'45'case'45'chain'45'aux_978 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain'45'aux_978 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_is'45'inl_46 -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v6
      C_is'45'inr_52 -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v4 v6
      C_is'45'other'45'coprod_62
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_case_68 v3 v4)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v2 v5 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.post-case-chain
d_post'45'case'45'chain_1014 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'chain_1014 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'chain_1014 v0 v1 v4 v5 v6 v7
du_post'45'case'45'chain_1014 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_510 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain_1014 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'comp_522
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    du_post'45'case'45'chain'45'aux_978 (coe v0) (coe v1) (coe v12)
                    (coe v2) (coe v3) (coe v14) (coe v15)
                    (coe du_coprodView_406 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_530
        -> coe
             du_optimize'45'compose'45'second_726
             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.post-case-aux
d_post'45'case'45'aux_1044 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'aux_1044 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'aux_1044 v0 v1 v4 v5 v6 v7
du_post'45'case'45'aux_1044 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'aux_1044 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'inl_46 -> coe v2
      C_is'45'inr_52 -> coe v3
      C_is'45'other'45'coprod_62
        -> coe
             du_post'45'case'45'chain_1014 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe du_chainView_538 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_1068 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_1068 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_1068 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_1068 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_1068 v0 v1 v2 v3 v4
  = coe
      du_post'45'case'45'aux_1044 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe du_coprodView_406 (coe v4))
-- Once.Optimize.terminal-drop
d_terminal'45'drop_1082 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_terminal'45'drop_1082 ~v0 v1 v2 v3
  = du_terminal'45'drop_1082 v1 v2 v3
du_terminal'45'drop_1082 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_terminal'45'drop_1082 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28 v0
             (coe MAlonzo.Code.Once.IR.C_terminal_72) v1
      else coe MAlonzo.Code.Once.IR.C_terminal_72
-- Once.Optimize.compose-aux
d_compose'45'aux_1098 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeFirstView_68 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'aux_1098 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_cf'45'id_72 -> coe v4
      C_cf'45'terminal_76
        -> coe
             du_terminal'45'drop_1082 (coe v1) (coe v4)
             (coe d_has'45'effect'63'_680 (coe v0) (coe v1) (coe v4))
      C_cf'45'fst_82
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'fst_842 (coe v0) (coe v2) (coe v9) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'snd_88
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'snd_956 (coe v0) (coe v8) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'case_100
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_case_68 v16 v17
                      -> coe
                           du_optimize'45'post'45'case_1068 (coe v11) (coe v12) (coe v16)
                           (coe v17) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'comp_112
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14
                    (coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v15 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'other_120
        -> coe
             du_optimize'45'compose'45'second_726 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose
d_optimize'45'compose_1130 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_1130 v0 v1 v2 v3 v4
  = coe
      d_compose'45'aux_1098 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe du_composeFirstView_416 (coe v3))
-- Once.Optimize.unit-like-aux
d_unit'45'like'45'aux_1140 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_unit'45'like'45'aux_1140 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d_not_22
                       (coe d_has'45'effect'63'_680 (coe v0) (coe v1) (coe v2)))
             else coe seq (coe v5) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.unit-like
d_unit'45'like_1150 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_unit'45'like_1150 v0 v1 v2
  = coe
      d_unit'45'like'45'aux_1140 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v1)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
-- Once.Optimize.void-like
d_void'45'like_1160 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_void'45'like_1160 v0 ~v1 ~v2 = du_void'45'like_1160 v0
du_void'45'like_1160 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
du_void'45'like_1160 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.C_Void_18))
-- Once.Optimize.fst-like-aux
d_fst'45'like'45'aux_1170 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_148 -> Bool
d_fst'45'like'45'aux_1170 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_154 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'snd_160
        -> coe
             d_unit'45'like_1150
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      C_fsv'45'other_168
        -> coe
             d_unit'45'like_1150
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v0)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-like-aux
d_snd'45'like'45'aux_1184 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_148 -> Bool
d_snd'45'like'45'aux_1184 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_154
        -> coe
             d_unit'45'like_1150
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      C_fsv'45'snd_160 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'other_168
        -> coe
             d_unit'45'like_1150
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inl-like-aux
d_inl'45'like'45'aux_1198 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_174 -> Bool
d_inl'45'like'45'aux_1198 v0 ~v1 ~v2 v3
  = du_inl'45'like'45'aux_1198 v0 v3
du_inl'45'like'45'aux_1198 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_174 -> Bool
du_inl'45'like'45'aux_1198 v0 v1
  = case coe v1 of
      C_iiv'45'inl_180 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'inr_186 -> coe du_void'45'like_1160 (coe v0)
      C_iiv'45'other_194 -> coe du_void'45'like_1160 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inr-like-aux
d_inr'45'like'45'aux_1212 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_174 -> Bool
d_inr'45'like'45'aux_1212 v0 v1 ~v2 v3
  = du_inr'45'like'45'aux_1212 v0 v1 v3
du_inr'45'like'45'aux_1212 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_174 -> Bool
du_inr'45'like'45'aux_1212 v0 v1 v2
  = case coe v2 of
      C_iiv'45'inl_180 -> coe du_void'45'like_1160 (coe v0)
      C_iiv'45'inr_186 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'other_194 -> coe du_void'45'like_1160 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.eta-pair
d_eta'45'pair_1228 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'pair_1228 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'pair_1228 v2 v3 v4 v5
du_eta'45'pair_1228 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'pair_1228 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
      else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
-- Once.Optimize.pair-aux
d_pair'45'aux_1248 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pair'45'aux_1248 v0 v1 ~v2 v3 v4 v5
  = du_pair'45'aux_1248 v0 v1 v3 v4 v5
du_pair'45'aux_1248 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_pair'45'aux_1248 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'pair_1228 (coe v2) (coe v3)
                       (coe
                          d_fst'45'like'45'aux_1170 (coe v0) (coe v1) (coe v2)
                          (coe du_fstSndView_586 (coe v2)))
                       (coe
                          d_snd'45'like'45'aux_1184 (coe v0) (coe v1) (coe v3)
                          (coe du_fstSndView_586 (coe v3))))
             else coe
                    seq (coe v6)
                    (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_1264 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_1264 v0 v1 v2 v3 v4
  = coe
      du_pair'45'aux_1248 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
-- Once.Optimize.eta-case
d_eta'45'case_1284 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'case_1284 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'case_1284 v2 v3 v4 v5
du_eta'45'case_1284 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'case_1284 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
      else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
-- Once.Optimize.case-aux
d_case'45'aux_1304 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_case'45'aux_1304 v0 v1 ~v2 v3 v4 v5
  = du_case'45'aux_1304 v0 v1 v3 v4 v5
du_case'45'aux_1304 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_case'45'aux_1304 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'case_1284 (coe v2) (coe v3)
                       (coe
                          du_inl'45'like'45'aux_1198 (coe v0)
                          (coe du_inlInrView_634 (coe v2)))
                       (coe
                          du_inr'45'like'45'aux_1212 (coe v0) (coe v1)
                          (coe du_inlInrView_634 (coe v3))))
             else coe seq (coe v6) (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1320 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1320 v0 v1 v2 v3 v4
  = coe
      du_case'45'aux_1304 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1)))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1336 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1336 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_1130 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1342 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1342 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    d_optimize'45'pair_1264 (coe v8) (coe v9) (coe v0)
                    (coe d_optimize'45'once_1342 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1342 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.IR.C_snd_48 -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.IR.C_inl_54 -> coe MAlonzo.Code.Once.IR.C_inl_54
      MAlonzo.Code.Once.IR.C_inr_60 -> coe MAlonzo.Code.Once.IR.C_inr_60
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    d_optimize'45'case_1320 (coe v8) (coe v9) (coe v1)
                    (coe d_optimize'45'once_1342 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1342 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_84
                    (d_optimize'45'once_1342
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Once.IR.C_apply_90
      MAlonzo.Code.Once.IR.C_In_94 v4
        -> coe MAlonzo.Code.Once.IR.C_In_94 v4
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_106 v4
                           (d_optimize'45'once_1342
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10)
                                    (coe v1)))
                              (coe v1) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4
        -> coe MAlonzo.Code.Once.IR.C_Out_110 v4
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Ana_122 v4
                           (d_optimize'45'once_1342
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10) (coe v9))
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_Iter_130
                    (d_optimize'45'once_1342
                       (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v8))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_134 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                     (coe (0 :: Integer)) (coe v3)
                     (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                       else coe seq (coe v8) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_Call_146 v5
        -> coe MAlonzo.Code.Once.IR.C_Call_146 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_1342 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1342 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
              (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1)))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_irtyTag_198
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v1))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_irtyTag_198
                             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_680
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1336 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
                             else coe MAlonzo.Code.Once.IR.C_terminal_72))
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_206
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v6 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                              (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt
                                              (coe MAlonzo.Code.Once.IRTy.d_irtyTag_198 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_irtyTag_198
                                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_1336 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1460 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1460 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1460 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1342 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1472 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1472 v0 v1
  = coe d_optimize'45'n_1460 (coe v0) (coe v1) (coe (10 :: Integer))
