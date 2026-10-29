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
    C_cf'45'apply_118 | C_cf'45'other_126
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_132 a0 a1 a2 = ()
data T_ComposeSecondView_132
  = C_cs'45'id_136 | C_cs'45'initial_140 | C_cs'45'other_148
-- Once.Optimize.CurryView
d_CurryView_156 a0 a1 a2 a3 = ()
data T_CurryView_156
  = C_is'45'curry_166 | C_is'45'other'45'curry_176
-- Once.Optimize.FstSndView
d_FstSndView_182 a0 a1 a2 = ()
data T_FstSndView_182
  = C_fsv'45'fst_188 | C_fsv'45'snd_194 | C_fsv'45'other_202
-- Once.Optimize.InlInrView
d_InlInrView_208 a0 a1 a2 = ()
data T_InlInrView_208
  = C_iiv'45'inl_214 | C_iiv'45'inr_220 | C_iiv'45'other_228
-- Once.Optimize.pairView-gen
d_pairView'45'gen_242 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_10
d_pairView'45'gen_242 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_242 v2
du_pairView'45'gen_242 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
du_pairView'45'gen_242 v0
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
d_pairView_334 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
d_pairView_334 ~v0 ~v1 ~v2 v3 = du_pairView_334 v3
du_pairView_334 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_10
du_pairView_334 v0 = coe du_pairView'45'gen_242 (coe v0)
-- Once.Optimize.curryView-gen
d_curryView'45'gen_350 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CurryView_156
d_curryView'45'gen_350 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_curryView'45'gen_350 v2
du_curryView'45'gen_350 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_156
du_curryView'45'gen_350 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_is'45'curry_166
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_Iter_130 v4
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_const_134 v2 v3
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3
        -> coe C_is'45'other'45'curry_176
      MAlonzo.Code.Once.IR.C_Call_146 v3
        -> coe C_is'45'other'45'curry_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.curryView
d_curryView_442 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_156
d_curryView_442 ~v0 ~v1 ~v2 v3 = du_curryView_442 v3
du_curryView_442 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_156
du_curryView_442 v0 = coe du_curryView'45'gen_350 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_458 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CoprodView_40
d_coprodView'45'gen_458 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_458 v2
du_coprodView'45'gen_458 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
du_coprodView'45'gen_458 v0
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
d_coprodView_548 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
d_coprodView_548 ~v0 ~v1 ~v2 v3 = du_coprodView_548 v3
du_coprodView_548 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_40
du_coprodView_548 v0 = coe du_coprodView'45'gen_458 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_558 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_68
d_composeFirstView_558 ~v0 ~v1 v2 = du_composeFirstView_558 v2
du_composeFirstView_558 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_68
du_composeFirstView_558 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_72
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_cf'45'comp_112
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_82
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_88
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_100
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_76
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cf'45'apply_118
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cf'45'other_126
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cf'45'other_126
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_606 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_132
d_composeSecondView_606 ~v0 ~v1 v2 = du_composeSecondView_606 v2
du_composeSecondView_606 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_132
du_composeSecondView_606 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_136
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_140
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_cs'45'other_148
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_cs'45'other_148
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.ChainView
d_ChainView_652 a0 a1 a2 = ()
data T_ChainView_652 = C_is'45'comp_664 | C_not'45'comp_672
-- Once.Optimize.chainView
d_chainView_680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_652
d_chainView_680 ~v0 ~v1 v2 = du_chainView_680 v2
du_chainView_680 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_652
du_chainView_680 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_is'45'comp_664
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_not'45'comp_672
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_not'45'comp_672
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_728 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_182
d_fstSndView_728 ~v0 ~v1 v2 = du_fstSndView_728 v2
du_fstSndView_728 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_182
du_fstSndView_728 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_188
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_194
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_fsv'45'other_202
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_fsv'45'other_202
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_776 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_208
d_inlInrView_776 ~v0 ~v1 v2 = du_inlInrView_776 v2
du_inlInrView_776 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_208
du_inlInrView_776 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_214
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_220
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_curry_84 v4 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_apply_90 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_In_94 v2 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v2 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_Cata_106 v2 v5 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_Out_110 v2 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v2 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_Ana_122 v2 v5 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_Iter_130 v4 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_const_134 v2 v3 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_SigOp_140 v1 v2 v3 -> coe C_iiv'45'other_228
      MAlonzo.Code.Once.IR.C_Call_146 v3 -> coe C_iiv'45'other_228
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_822 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_822 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_822 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_822 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v9) (coe v7))
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
                    (coe d_has'45'effect'63'_822 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_822 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    d_has'45'effect'63'_822
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
                           d_has'45'effect'63'_822
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
                           d_has'45'effect'63'_822 (coe v0)
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
d_compose'45'second'45'aux_852 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_132 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'second'45'aux_852 ~v0 v1 ~v2 v3 v4 v5
  = du_compose'45'second'45'aux_852 v1 v3 v4 v5
du_compose'45'second'45'aux_852 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_132 -> MAlonzo.Code.Once.IR.T_IR_16
du_compose'45'second'45'aux_852 v0 v1 v2 v3
  = case coe v3 of
      C_cs'45'id_136 -> coe v1
      C_cs'45'initial_140 -> coe MAlonzo.Code.Once.IR.C_initial_76
      C_cs'45'other_148
        -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_868 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_868 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_868 v1 v3 v4
du_optimize'45'compose'45'second_868 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_868 v0 v1 v2
  = coe
      du_compose'45'second'45'aux_852 (coe v0) (coe v1) (coe v2)
      (coe du_composeSecondView_606 (coe v2))
-- Once.Optimize.fst-pair
d_fst'45'pair_884 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'pair_884 ~v0 v1 v2 v3 v4 v5
  = du_fst'45'pair_884 v1 v2 v3 v4 v5
du_fst'45'pair_884 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'pair_884 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v2
-- Once.Optimize.fst-chain-pair
d_fst'45'chain'45'pair_908 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'pair_908 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_fst'45'chain'45'pair_908 v1 v2 v3 v4 v5 v6 v7
du_fst'45'chain'45'pair_908 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'pair_908 v0 v1 v2 v3 v4 v5 v6
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
d_fst'45'chain'45'aux_934 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'aux_934 ~v0 v1 v2 v3 v4 v5 v6
  = du_fst'45'chain'45'aux_934 v1 v2 v3 v4 v5 v6
du_fst'45'chain'45'aux_934 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'aux_934 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_fst'45'chain'45'pair_908 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v2) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-chain
d_fst'45'chain_954 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain_954 ~v0 v1 v2 v3 v4
  = du_fst'45'chain_954 v1 v2 v3 v4
du_fst'45'chain_954 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain_954 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_664
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_fst'45'chain'45'aux_934 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_334 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             du_optimize'45'compose'45'second_868
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-aux
d_fst'45'aux_970 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'aux_970 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_fst'45'pair_884 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v2) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             du_fst'45'chain_954 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_680 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_984 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_984 v0 v1 v2 v3
  = coe
      d_fst'45'aux_970 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_334 (coe v3))
-- Once.Optimize.snd-pair
d_snd'45'pair_998 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'pair_998 ~v0 v1 v2 v3 v4 v5
  = du_snd'45'pair_998 v1 v2 v3 v4 v5
du_snd'45'pair_998 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'pair_998 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v3
-- Once.Optimize.snd-chain-pair
d_snd'45'chain'45'pair_1022 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'pair_1022 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_snd'45'chain'45'pair_1022 v1 v2 v3 v4 v5 v6 v7
du_snd'45'chain'45'pair_1022 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'pair_1022 v0 v1 v2 v3 v4 v5 v6
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
d_snd'45'chain'45'aux_1048 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'aux_1048 ~v0 v1 v2 v3 v4 v5 v6
  = du_snd'45'chain'45'aux_1048 v1 v2 v3 v4 v5 v6
du_snd'45'chain'45'aux_1048 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'aux_1048 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_snd'45'chain'45'pair_1022 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v1) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-chain
d_snd'45'chain_1068 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain_1068 ~v0 v1 v2 v3 v4
  = du_snd'45'chain_1068 v1 v2 v3 v4
du_snd'45'chain_1068 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain_1068 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_664
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_snd'45'chain'45'aux_1048 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_334 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             du_optimize'45'compose'45'second_868
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-aux
d_snd'45'aux_1084 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'aux_1084 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_snd'45'pair_998 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_822 (coe v0) (coe v1) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             du_snd'45'chain_1068 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_680 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-snd
d_optimize'45'snd_1098 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_1098 v0 v1 v2 v3
  = coe
      d_snd'45'aux_1084 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_334 (coe v3))
-- Once.Optimize.post-case-chain-aux
d_post'45'case'45'chain'45'aux_1120 ::
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
d_post'45'case'45'chain'45'aux_1120 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_post'45'case'45'chain'45'aux_1120 v0 v1 v4 v5 v6 v7 v8 v9
du_post'45'case'45'chain'45'aux_1120 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain'45'aux_1120 v0 v1 v2 v3 v4 v5 v6 v7
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
d_post'45'case'45'chain_1156 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'chain_1156 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'chain_1156 v0 v1 v4 v5 v6 v7
du_post'45'case'45'chain_1156 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain_1156 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'comp_664
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    du_post'45'case'45'chain'45'aux_1120 (coe v0) (coe v1) (coe v12)
                    (coe v2) (coe v3) (coe v14) (coe v15)
                    (coe du_coprodView_548 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             du_optimize'45'compose'45'second_868
             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.post-case-aux
d_post'45'case'45'aux_1186 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'aux_1186 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'aux_1186 v0 v1 v4 v5 v6 v7
du_post'45'case'45'aux_1186 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_40 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'aux_1186 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'inl_46 -> coe v2
      C_is'45'inr_52 -> coe v3
      C_is'45'other'45'coprod_62
        -> coe
             du_post'45'case'45'chain_1156 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe du_chainView_680 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_1210 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_1210 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_1210 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_1210 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_1210 v0 v1 v2 v3 v4
  = coe
      du_post'45'case'45'aux_1186 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe du_coprodView_548 (coe v4))
-- Once.Optimize.beta-head
d_beta'45'head_1232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'head_1232 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_beta'45'head_1232 v1 v2 v3 v4 v5 v6 v7
du_beta'45'head_1232 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'head_1232 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'curry_166
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_curry_84 v14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) v14
                    (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_176
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-bare
d_beta'45'bare_1256 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'bare_1256 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'curry_166
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_curry_84 v13
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) v13
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe MAlonzo.Code.Once.IR.C_id_20) v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_176
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.closure-beta
d_closure'45'beta_1276 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_closure'45'beta_1276 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'comp_664
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    du_beta'45'head_1232 (coe v12) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4) (coe du_curryView_442 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             d_beta'45'bare_1256 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe du_curryView_442 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-head-chain
d_beta'45'head'45'chain_1306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'head'45'chain_1306 ~v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_beta'45'head'45'chain_1306 v1 v2 v3 v4 v5 v6 v7 v8 v9
du_beta'45'head'45'chain_1306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'head'45'chain_1306 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_is'45'curry_166
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_curry_84 v16
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2)) v16
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28 v0
                       (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v5 v6) v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_176
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v2) (coe v3))
                (coe v2))
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v0
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                   (coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v4 v5) v6)
                v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-bare-chain
d_beta'45'bare'45'chain_1338 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'bare'45'chain_1338 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_beta'45'bare'45'chain_1338 v1 v2 v3 v4 v5 v6 v7
du_beta'45'bare'45'chain_1338 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_156 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'bare'45'chain_1338 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'curry_166
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_curry_84 v14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) v14
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28 v0
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe MAlonzo.Code.Once.IR.C_id_20) v4)
                       v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_176
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v0
                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v3 v4) v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.closure-beta-chain
d_closure'45'beta'45'chain_1366 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_closure'45'beta'45'chain_1366 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_closure'45'beta'45'chain_1366 v1 v2 v3 v4 v5 v6 v7
du_closure'45'beta'45'chain_1366 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
du_closure'45'beta'45'chain_1366 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'comp_664
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v13 v15 v16
               -> coe
                    du_beta'45'head'45'chain_1306 (coe v0) (coe v13) (coe v1) (coe v2)
                    (coe v15) (coe v16) (coe v4) (coe v5)
                    (coe du_curryView_442 (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             du_beta'45'bare'45'chain_1338 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe du_curryView_442 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-chain-aux
d_apply'45'chain'45'aux_1394 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'chain'45'aux_1394 ~v0 v1 v2 v3 v4 v5 v6
  = du_apply'45'chain'45'aux_1394 v1 v2 v3 v4 v5 v6
du_apply'45'chain'45'aux_1394 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_apply'45'chain'45'aux_1394 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_closure'45'beta'45'chain_1366 (coe v0) (coe v1) (coe v2)
                    (coe v14) (coe v15) (coe v4) (coe du_chainView_680 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.IR.C_apply_90)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-chain
d_apply'45'chain_1414 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'chain_1414 ~v0 v1 v2 v3 v4
  = du_apply'45'chain_1414 v1 v2 v3 v4
du_apply'45'chain_1414 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_652 -> MAlonzo.Code.Once.IR.T_IR_16
du_apply'45'chain_1414 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_664
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_apply'45'chain'45'aux_1394 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_334 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_672
        -> coe
             du_optimize'45'compose'45'second_868
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                (coe v0))
             (coe MAlonzo.Code.Once.IR.C_apply_90) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-aux
d_apply'45'aux_1430 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'aux_1430 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_22
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    d_closure'45'beta_1276 (coe v0) (coe v1) (coe v2) (coe v13)
                    (coe v14) (coe du_chainView_680 (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_32
        -> coe
             du_apply'45'chain_1414 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_680 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-apply
d_optimize'45'apply_1444 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'apply_1444 v0 v1 v2 v3
  = coe
      d_apply'45'aux_1430 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_334 (coe v3))
-- Once.Optimize.terminal-drop
d_terminal'45'drop_1454 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_terminal'45'drop_1454 ~v0 v1 v2 v3
  = du_terminal'45'drop_1454 v1 v2 v3
du_terminal'45'drop_1454 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_terminal'45'drop_1454 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28 v0
             (coe MAlonzo.Code.Once.IR.C_terminal_72) v1
      else coe MAlonzo.Code.Once.IR.C_terminal_72
-- Once.Optimize.compose-aux
d_compose'45'aux_1470 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeFirstView_68 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'aux_1470 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_cf'45'id_72 -> coe v4
      C_cf'45'terminal_76
        -> coe
             du_terminal'45'drop_1454 (coe v1) (coe v4)
             (coe d_has'45'effect'63'_822 (coe v0) (coe v1) (coe v4))
      C_cf'45'fst_82
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'fst_984 (coe v0) (coe v2) (coe v9) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'snd_88
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'snd_1098 (coe v0) (coe v8) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'case_100
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_case_68 v16 v17
                      -> coe
                           du_optimize'45'post'45'case_1210 (coe v11) (coe v12) (coe v16)
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
      C_cf'45'apply_118
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                      -> coe
                           d_optimize'45'apply_1444 (coe v0) (coe v10) (coe v2) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'other_126
        -> coe
             du_optimize'45'compose'45'second_868 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose
d_optimize'45'compose_1504 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_1504 v0 v1 v2 v3 v4
  = coe
      d_compose'45'aux_1470 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe du_composeFirstView_558 (coe v3))
-- Once.Optimize.unit-like-aux
d_unit'45'like'45'aux_1514 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_unit'45'like'45'aux_1514 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d_not_22
                       (coe d_has'45'effect'63'_822 (coe v0) (coe v1) (coe v2)))
             else coe seq (coe v5) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.unit-like
d_unit'45'like_1524 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_unit'45'like_1524 v0 v1 v2
  = coe
      d_unit'45'like'45'aux_1514 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v1)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
-- Once.Optimize.void-like
d_void'45'like_1534 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_void'45'like_1534 v0 ~v1 ~v2 = du_void'45'like_1534 v0
du_void'45'like_1534 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
du_void'45'like_1534 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.C_Void_18))
-- Once.Optimize.fst-like-aux
d_fst'45'like'45'aux_1544 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_182 -> Bool
d_fst'45'like'45'aux_1544 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_188 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'snd_194
        -> coe
             d_unit'45'like_1524
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      C_fsv'45'other_202
        -> coe
             d_unit'45'like_1524
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v0)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-like-aux
d_snd'45'like'45'aux_1558 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_182 -> Bool
d_snd'45'like'45'aux_1558 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_188
        -> coe
             d_unit'45'like_1524
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      C_fsv'45'snd_194 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'other_202
        -> coe
             d_unit'45'like_1524
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inl-like-aux
d_inl'45'like'45'aux_1572 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_208 -> Bool
d_inl'45'like'45'aux_1572 v0 ~v1 ~v2 v3
  = du_inl'45'like'45'aux_1572 v0 v3
du_inl'45'like'45'aux_1572 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_208 -> Bool
du_inl'45'like'45'aux_1572 v0 v1
  = case coe v1 of
      C_iiv'45'inl_214 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'inr_220 -> coe du_void'45'like_1534 (coe v0)
      C_iiv'45'other_228 -> coe du_void'45'like_1534 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inr-like-aux
d_inr'45'like'45'aux_1586 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_208 -> Bool
d_inr'45'like'45'aux_1586 v0 v1 ~v2 v3
  = du_inr'45'like'45'aux_1586 v0 v1 v3
du_inr'45'like'45'aux_1586 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_208 -> Bool
du_inr'45'like'45'aux_1586 v0 v1 v2
  = case coe v2 of
      C_iiv'45'inl_214 -> coe du_void'45'like_1534 (coe v0)
      C_iiv'45'inr_220 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'other_228 -> coe du_void'45'like_1534 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.eta-pair
d_eta'45'pair_1602 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'pair_1602 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'pair_1602 v2 v3 v4 v5
du_eta'45'pair_1602 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'pair_1602 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
      else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
-- Once.Optimize.pair-aux
d_pair'45'aux_1622 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pair'45'aux_1622 v0 v1 ~v2 v3 v4 v5
  = du_pair'45'aux_1622 v0 v1 v3 v4 v5
du_pair'45'aux_1622 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_pair'45'aux_1622 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'pair_1602 (coe v2) (coe v3)
                       (coe
                          d_fst'45'like'45'aux_1544 (coe v0) (coe v1) (coe v2)
                          (coe du_fstSndView_728 (coe v2)))
                       (coe
                          d_snd'45'like'45'aux_1558 (coe v0) (coe v1) (coe v3)
                          (coe du_fstSndView_728 (coe v3))))
             else coe
                    seq (coe v6)
                    (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_1638 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_1638 v0 v1 v2 v3 v4
  = coe
      du_pair'45'aux_1622 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
-- Once.Optimize.eta-case
d_eta'45'case_1658 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'case_1658 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'case_1658 v2 v3 v4 v5
du_eta'45'case_1658 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'case_1658 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
      else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
-- Once.Optimize.case-aux
d_case'45'aux_1678 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_case'45'aux_1678 v0 v1 ~v2 v3 v4 v5
  = du_case'45'aux_1678 v0 v1 v3 v4 v5
du_case'45'aux_1678 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_case'45'aux_1678 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'case_1658 (coe v2) (coe v3)
                       (coe
                          du_inl'45'like'45'aux_1572 (coe v0)
                          (coe du_inlInrView_776 (coe v2)))
                       (coe
                          du_inr'45'like'45'aux_1586 (coe v0) (coe v1)
                          (coe du_inlInrView_776 (coe v3))))
             else coe seq (coe v6) (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1694 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1694 v0 v1 v2 v3 v4
  = coe
      du_case'45'aux_1678 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__200 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1)))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1710 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1710 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_1504 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1716 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1716 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    d_optimize'45'pair_1638 (coe v8) (coe v9) (coe v0)
                    (coe d_optimize'45'once_1716 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1716 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.IR.C_snd_48 -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.IR.C_inl_54 -> coe MAlonzo.Code.Once.IR.C_inl_54
      MAlonzo.Code.Once.IR.C_inr_60 -> coe MAlonzo.Code.Once.IR.C_inr_60
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    d_optimize'45'case_1694 (coe v8) (coe v9) (coe v1)
                    (coe d_optimize'45'once_1716 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1716 (coe v9) (coe v1) (coe v7))
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
                    (d_optimize'45'once_1716
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
                           (d_optimize'45'once_1716
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
                           (d_optimize'45'once_1716
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
                    (d_optimize'45'once_1716
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
d_optimize'45'once_1716 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1716 v0 v1 v2
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
                              = d_has'45'effect'63'_822
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1710 (coe v0)
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
                                              d_optimize'45'once'45'structural_1710 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1834 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1834 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1834 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1716 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1846 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1846 v0 v1
  = coe d_optimize'45'n_1834 (coe v0) (coe v1) (coe (10 :: Integer))
