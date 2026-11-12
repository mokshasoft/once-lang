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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Optimize.PairView
d_PairView_12 a0 a1 a2 a3 = ()
data T_PairView_12 = C_is'45'pair_24 | C_is'45'other'45'pair_34
-- Once.Optimize.CoprodView
d_CoprodView_42 a0 a1 a2 a3 = ()
data T_CoprodView_42
  = C_is'45'inl_48 | C_is'45'inr_54 | C_is'45'other'45'coprod_64
-- Once.Optimize.ComposeFirstView
d_ComposeFirstView_70 a0 a1 a2 = ()
data T_ComposeFirstView_70
  = C_cf'45'id_74 | C_cf'45'terminal_78 | C_cf'45'fst_84 |
    C_cf'45'snd_90 | C_cf'45'case_102 | C_cf'45'comp_114 |
    C_cf'45'apply_120 | C_cf'45'other_128
-- Once.Optimize.ComposeSecondView
d_ComposeSecondView_134 a0 a1 a2 = ()
data T_ComposeSecondView_134
  = C_cs'45'id_138 | C_cs'45'initial_142 | C_cs'45'other_150
-- Once.Optimize.CurryView
d_CurryView_158 a0 a1 a2 a3 a4 = ()
data T_CurryView_158
  = C_is'45'curry_168 | C_is'45'other'45'curry_178
-- Once.Optimize.FstSndView
d_FstSndView_184 a0 a1 a2 = ()
data T_FstSndView_184
  = C_fsv'45'fst_190 | C_fsv'45'snd_196 | C_fsv'45'other_204
-- Once.Optimize.InlInrView
d_InlInrView_210 a0 a1 a2 = ()
data T_InlInrView_210
  = C_iiv'45'inl_216 | C_iiv'45'inr_222 | C_iiv'45'other_230
-- Once.Optimize.pairView-gen
d_pairView'45'gen_244 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_PairView_12
d_pairView'45'gen_244 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_pairView'45'gen_244 v2
du_pairView'45'gen_244 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_12
du_pairView'45'gen_244 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'pair_24
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_const_138 v2 v3
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3
        -> coe C_is'45'other'45'pair_34
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_is'45'other'45'pair_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.pairView
d_pairView_336 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_12
d_pairView_336 ~v0 ~v1 ~v2 v3 = du_pairView_336 v3
du_pairView_336 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_PairView_12
du_pairView_336 v0 = coe du_pairView'45'gen_244 (coe v0)
-- Once.Optimize.curryView-gen
d_curryView'45'gen_352 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CurryView_158
d_curryView'45'gen_352 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6
  = du_curryView'45'gen_352 v3
du_curryView'45'gen_352 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_158
du_curryView'45'gen_352 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_is'45'curry_168
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_Iter_134 v4
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_const_138 v2 v3
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3
        -> coe C_is'45'other'45'curry_178
      MAlonzo.Code.Once.IR.C_Call_150 v3
        -> coe C_is'45'other'45'curry_178
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.curryView
d_curryView_444 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_158
d_curryView_444 ~v0 ~v1 ~v2 ~v3 v4 = du_curryView_444 v4
du_curryView_444 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_CurryView_158
du_curryView_444 v0 = coe du_curryView'45'gen_352 (coe v0)
-- Once.Optimize.coprodView-gen
d_coprodView'45'gen_460 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_CoprodView_42
d_coprodView'45'gen_460 ~v0 ~v1 v2 ~v3 ~v4 ~v5
  = du_coprodView'45'gen_460 v2
du_coprodView'45'gen_460 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_42
du_coprodView'45'gen_460 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_is'45'inl_48
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_is'45'inr_54
      MAlonzo.Code.Once.IR.C_case_68 v4 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_curry_86 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_Iter_134 v4
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_const_138 v2 v3
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3
        -> coe C_is'45'other'45'coprod_64
      MAlonzo.Code.Once.IR.C_Call_150 v3
        -> coe C_is'45'other'45'coprod_64
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.coprodView
d_coprodView_550 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_42
d_coprodView_550 ~v0 ~v1 ~v2 v3 = du_coprodView_550 v3
du_coprodView_550 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_CoprodView_42
du_coprodView_550 v0 = coe du_coprodView'45'gen_460 (coe v0)
-- Once.Optimize.composeFirstView
d_composeFirstView_560 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_70
d_composeFirstView_560 ~v0 ~v1 v2 = du_composeFirstView_560 v2
du_composeFirstView_560 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeFirstView_70
du_composeFirstView_560 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cf'45'id_74
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_cf'45'comp_114
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cf'45'fst_84
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cf'45'snd_90
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cf'45'case_102
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cf'45'terminal_78
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_cf'45'apply_120
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_const_138 v2 v3 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3 -> coe C_cf'45'other_128
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_cf'45'other_128
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.composeSecondView
d_composeSecondView_608 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_134
d_composeSecondView_608 ~v0 ~v1 v2 = du_composeSecondView_608 v2
du_composeSecondView_608 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ComposeSecondView_134
du_composeSecondView_608 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_cs'45'id_138
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_cs'45'initial_142
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_const_138 v2 v3 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3 -> coe C_cs'45'other_150
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_cs'45'other_150
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.ChainView
d_ChainView_654 a0 a1 a2 = ()
data T_ChainView_654 = C_is'45'comp_666 | C_not'45'comp_674
-- Once.Optimize.chainView
d_chainView_682 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_654
d_chainView_682 ~v0 ~v1 v2 = du_chainView_682 v2
du_chainView_682 :: MAlonzo.Code.Once.IR.T_IR_16 -> T_ChainView_654
du_chainView_682 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5 -> coe C_is'45'comp_666
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_const_138 v2 v3 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3 -> coe C_not'45'comp_674
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_not'45'comp_674
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fstSndView
d_fstSndView_730 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_184
d_fstSndView_730 ~v0 ~v1 v2 = du_fstSndView_730 v2
du_fstSndView_730 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_184
du_fstSndView_730 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_fsv'45'fst_190
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_fsv'45'snd_196
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_const_138 v2 v3 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3 -> coe C_fsv'45'other_204
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_fsv'45'other_204
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inlInrView
d_inlInrView_778 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_210
d_inlInrView_778 ~v0 ~v1 v2 = du_inlInrView_778 v2
du_inlInrView_778 ::
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_210
du_inlInrView_778 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C__'8728'__28 v2 v4 v5
        -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5
        -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_iiv'45'inl_216
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_iiv'45'inr_222
      MAlonzo.Code.Once.IR.C_case_68 v4 v5 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_curry_86 v5 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_In_98 v2 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v2 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_Cata_110 v2 v5 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_Out_114 v2 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v2 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_Ana_126 v2 v5 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_Iter_134 v4 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_const_138 v2 v3 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_SigOp_144 v1 v2 v3 -> coe C_iiv'45'other_230
      MAlonzo.Code.Once.IR.C_Call_150 v3 -> coe C_iiv'45'other_230
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.has-effect?
d_has'45'effect'63'_824 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_has'45'effect'63'_824 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'effect'63'_824 (coe v4) (coe v1) (coe v6))
             (coe d_has'45'effect'63'_824 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v8) (coe v6))
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v9) (coe v7))
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
                    (coe d_has'45'effect'63'_824 (coe v8) (coe v1) (coe v6))
                    (coe d_has'45'effect'63'_824 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_curry_86 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v8 v9 v10
               -> coe
                    d_has'45'effect'63'_824
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8))
                    (coe v10) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_In_98 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Cata_110 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           d_has'45'effect'63'_824
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v10) (coe v1)))
                           (coe v1) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_Ana_126 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           d_has'45'effect'63'_824 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v10) (coe v9))
                           (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v6
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_const_138 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.IR.C_SigOp_144 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.IR.C_Call_150 v5
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.compose-second-aux
d_compose'45'second'45'aux_854 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_134 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'second'45'aux_854 ~v0 v1 ~v2 v3 v4 v5
  = du_compose'45'second'45'aux_854 v1 v3 v4 v5
du_compose'45'second'45'aux_854 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeSecondView_134 -> MAlonzo.Code.Once.IR.T_IR_16
du_compose'45'second'45'aux_854 v0 v1 v2 v3
  = case coe v3 of
      C_cs'45'id_138 -> coe v1
      C_cs'45'initial_142 -> coe MAlonzo.Code.Once.IR.C_initial_76
      C_cs'45'other_150
        -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose-second
d_optimize'45'compose'45'second_870 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose'45'second_870 ~v0 v1 ~v2 v3 v4
  = du_optimize'45'compose'45'second_870 v1 v3 v4
du_optimize'45'compose'45'second_870 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'compose'45'second_870 v0 v1 v2
  = coe
      du_compose'45'second'45'aux_854 (coe v0) (coe v1) (coe v2)
      (coe du_composeSecondView_608 (coe v2))
-- Once.Optimize.fst-pair
d_fst'45'pair_886 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'pair_886 ~v0 v1 v2 v3 v4 v5
  = du_fst'45'pair_886 v1 v2 v3 v4 v5
du_fst'45'pair_886 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'pair_886 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v2
-- Once.Optimize.fst-chain-pair
d_fst'45'chain'45'pair_910 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'pair_910 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_fst'45'chain'45'pair_910 v1 v2 v3 v4 v5 v6 v7
du_fst'45'chain'45'pair_910 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'pair_910 v0 v1 v2 v3 v4 v5 v6
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
d_fst'45'chain'45'aux_936 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain'45'aux_936 ~v0 v1 v2 v3 v4 v5 v6
  = du_fst'45'chain'45'aux_936 v1 v2 v3 v4 v5 v6
du_fst'45'chain'45'aux_936 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain'45'aux_936 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_24
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_fst'45'chain'45'pair_910 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v2) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-chain
d_fst'45'chain_956 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'chain_956 ~v0 v1 v2 v3 v4
  = du_fst'45'chain_956 v1 v2 v3 v4
du_fst'45'chain_956 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
du_fst'45'chain_956 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_666
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_fst'45'chain'45'aux_936 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_336 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             du_optimize'45'compose'45'second_870
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_fst_42) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.fst-aux
d_fst'45'aux_972 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_fst'45'aux_972 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_24
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_fst'45'pair_886 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v2) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             du_fst'45'chain_956 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_682 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-fst
d_optimize'45'fst_986 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'fst_986 v0 v1 v2 v3
  = coe
      d_fst'45'aux_972 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_336 (coe v3))
-- Once.Optimize.snd-pair
d_snd'45'pair_1000 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'pair_1000 ~v0 v1 v2 v3 v4 v5
  = du_snd'45'pair_1000 v1 v2 v3 v4 v5
du_snd'45'pair_1000 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'pair_1000 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      else coe v3
-- Once.Optimize.snd-chain-pair
d_snd'45'chain'45'pair_1024 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'pair_1024 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_snd'45'chain'45'pair_1024 v1 v2 v3 v4 v5 v6 v7
du_snd'45'chain'45'pair_1024 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'pair_1024 v0 v1 v2 v3 v4 v5 v6
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
d_snd'45'chain'45'aux_1050 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain'45'aux_1050 ~v0 v1 v2 v3 v4 v5 v6
  = du_snd'45'chain'45'aux_1050 v1 v2 v3 v4 v5 v6
du_snd'45'chain'45'aux_1050 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain'45'aux_1050 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_24
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    du_snd'45'chain'45'pair_1024 (coe v0) (coe v1) (coe v2) (coe v14)
                    (coe v15) (coe v4)
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v1) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-chain
d_snd'45'chain_1070 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'chain_1070 ~v0 v1 v2 v3 v4
  = du_snd'45'chain_1070 v1 v2 v3 v4
du_snd'45'chain_1070 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
du_snd'45'chain_1070 v0 v1 v2 v3
  = case coe v3 of
      C_is'45'comp_666
        -> case coe v2 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v10 v12 v13
               -> coe
                    du_snd'45'chain'45'aux_1050 (coe v10) (coe v0) (coe v1) (coe v12)
                    (coe v13) (coe du_pairView_336 (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             du_optimize'45'compose'45'second_870
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_48) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-aux
d_snd'45'aux_1086 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_snd'45'aux_1086 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'pair_24
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v13 v14
               -> coe
                    du_snd'45'pair_1000 (coe v1) (coe v2) (coe v13) (coe v14)
                    (coe d_has'45'effect'63'_824 (coe v0) (coe v1) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             du_snd'45'chain_1070 (coe v1) (coe v2) (coe v3)
             (coe du_chainView_682 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-snd
d_optimize'45'snd_1100 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'snd_1100 v0 v1 v2 v3
  = coe
      d_snd'45'aux_1086 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe du_pairView_336 (coe v3))
-- Once.Optimize.post-case-chain-aux
d_post'45'case'45'chain'45'aux_1122 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_42 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'chain'45'aux_1122 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_post'45'case'45'chain'45'aux_1122 v0 v1 v4 v5 v6 v7 v8 v9
du_post'45'case'45'chain'45'aux_1122 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_42 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain'45'aux_1122 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_is'45'inl_48 -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v0 v3 v6
      C_is'45'inr_54 -> coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v4 v6
      C_is'45'other'45'coprod_64
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_case_68 v3 v4)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v2 v5 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.post-case-chain
d_post'45'case'45'chain_1158 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'chain_1158 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'chain_1158 v0 v1 v4 v5 v6 v7
du_post'45'case'45'chain_1158 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'chain_1158 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'comp_666
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    du_post'45'case'45'chain'45'aux_1122 (coe v0) (coe v1) (coe v12)
                    (coe v2) (coe v3) (coe v14) (coe v15)
                    (coe du_coprodView_550 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             du_optimize'45'compose'45'second_870
             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.post-case-aux
d_post'45'case'45'aux_1188 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_42 -> MAlonzo.Code.Once.IR.T_IR_16
d_post'45'case'45'aux_1188 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_post'45'case'45'aux_1188 v0 v1 v4 v5 v6 v7
du_post'45'case'45'aux_1188 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CoprodView_42 -> MAlonzo.Code.Once.IR.T_IR_16
du_post'45'case'45'aux_1188 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'inl_48 -> coe v2
      C_is'45'inr_54 -> coe v3
      C_is'45'other'45'coprod_64
        -> coe
             du_post'45'case'45'chain_1158 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe du_chainView_682 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-post-case
d_optimize'45'post'45'case_1212 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'post'45'case_1212 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_optimize'45'post'45'case_1212 v0 v1 v4 v5 v6
du_optimize'45'post'45'case_1212 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_optimize'45'post'45'case_1212 v0 v1 v2 v3 v4
  = coe
      du_post'45'case'45'aux_1188 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe du_coprodView_550 (coe v4))
-- Once.Optimize.beta-head
d_beta'45'head_1234 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'head_1234 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_beta'45'head_1234 v0 v2 v3 v4 v5 v6 v7 v8
du_beta'45'head_1234 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'head_1234 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_is'45'curry_168
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_curry_86 v17
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2)) v17
                    (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v5 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_178
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v2) (coe v0)
                   (coe v3))
                (coe v2))
             (coe MAlonzo.Code.Once.IR.C_apply_94)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v4 v5) v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-bare
d_beta'45'bare_1258 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'bare_1258 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'curry_168
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_curry_86 v16
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2)) v16
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe MAlonzo.Code.Once.IR.C_id_20) v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_178
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v2) (coe v0)
                   (coe v3))
                (coe v2))
             (coe MAlonzo.Code.Once.IR.C_apply_94)
             (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.closure-beta
d_closure'45'beta_1278 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_closure'45'beta_1278 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'comp_666
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v13 v15 v16
               -> coe
                    du_beta'45'head_1234 (coe v0) (coe v13) (coe v2) (coe v3) (coe v15)
                    (coe v16) (coe v5) (coe du_curryView_444 (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             d_beta'45'bare_1258 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe du_curryView_444 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-head-chain
d_beta'45'head'45'chain_1308 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'head'45'chain_1308 v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_beta'45'head'45'chain_1308 v0 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_beta'45'head'45'chain_1308 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'head'45'chain_1308 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_is'45'curry_168
        -> case coe v5 of
             MAlonzo.Code.Once.IR.C_curry_86 v19
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v3)) v19
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28 v1
                       (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7) v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_178
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v3) (coe v0)
                   (coe v4))
                (coe v3))
             (coe MAlonzo.Code.Once.IR.C_apply_94)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v1
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                   (coe MAlonzo.Code.Once.IR.C__'8728'__28 v2 v5 v6) v7)
                v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.beta-bare-chain
d_beta'45'bare'45'chain_1340 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
d_beta'45'bare'45'chain_1340 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_beta'45'bare'45'chain_1340 v0 v2 v3 v4 v5 v6 v7 v8
du_beta'45'bare'45'chain_1340 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_CurryView_158 -> MAlonzo.Code.Once.IR.T_IR_16
du_beta'45'bare'45'chain_1340 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_is'45'curry_168
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_curry_86 v17
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v2)) v17
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28 v1
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe MAlonzo.Code.Once.IR.C_id_20) v5)
                       v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'curry_178
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v2) (coe v0)
                   (coe v3))
                (coe v2))
             (coe MAlonzo.Code.Once.IR.C_apply_94)
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28 v1
                (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v4 v5) v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.closure-beta-chain
d_closure'45'beta'45'chain_1368 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_closure'45'beta'45'chain_1368 v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_closure'45'beta'45'chain_1368 v0 v2 v3 v4 v5 v6 v7 v8
du_closure'45'beta'45'chain_1368 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
du_closure'45'beta'45'chain_1368 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_is'45'comp_666
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v14 v16 v17
               -> coe
                    du_beta'45'head'45'chain_1308 (coe v0) (coe v1) (coe v14) (coe v2)
                    (coe v3) (coe v16) (coe v17) (coe v5) (coe v6)
                    (coe du_curryView_444 (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             du_beta'45'bare'45'chain_1340 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe du_curryView_444 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-chain-aux
d_apply'45'chain'45'aux_1396 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'chain'45'aux_1396 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_apply'45'chain'45'aux_1396 v0 v2 v3 v4 v5 v6 v7
du_apply'45'chain'45'aux_1396 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
du_apply'45'chain'45'aux_1396 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_is'45'pair_24
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v15 v16
               -> coe
                    du_closure'45'beta'45'chain_1368 (coe v0) (coe v1) (coe v2)
                    (coe v3) (coe v15) (coe v16) (coe v5)
                    (coe du_chainView_682 (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v2) (coe v0)
                   (coe v3))
                (coe v2))
             (coe MAlonzo.Code.Once.IR.C_apply_94)
             (coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v4 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-chain
d_apply'45'chain_1416 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'chain_1416 v0 ~v1 v2 v3 v4 v5
  = du_apply'45'chain_1416 v0 v2 v3 v4 v5
du_apply'45'chain_1416 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ChainView_654 -> MAlonzo.Code.Once.IR.T_IR_16
du_apply'45'chain_1416 v0 v1 v2 v3 v4
  = case coe v4 of
      C_is'45'comp_666
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v11 v13 v14
               -> coe
                    du_apply'45'chain'45'aux_1396 (coe v0) (coe v11) (coe v1) (coe v2)
                    (coe v13) (coe v14) (coe du_pairView_336 (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_not'45'comp_674
        -> coe
             du_optimize'45'compose'45'second_870
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe
                   MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 (coe v1) (coe v0)
                   (coe v2))
                (coe v1))
             (coe MAlonzo.Code.Once.IR.C_apply_94) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.apply-aux
d_apply'45'aux_1432 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_PairView_12 -> MAlonzo.Code.Once.IR.T_IR_16
d_apply'45'aux_1432 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_is'45'pair_24
        -> case coe v4 of
             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v14 v15
               -> coe
                    d_closure'45'beta_1278 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe v14) (coe v15) (coe du_chainView_682 (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_is'45'other'45'pair_34
        -> coe
             du_apply'45'chain_1416 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe du_chainView_682 (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-apply
d_optimize'45'apply_1446 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'apply_1446 v0 v1 v2 v3 v4
  = coe
      d_apply'45'aux_1432 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe du_pairView_336 (coe v4))
-- Once.Optimize.terminal-drop
d_terminal'45'drop_1456 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_terminal'45'drop_1456 ~v0 v1 v2 v3
  = du_terminal'45'drop_1456 v1 v2 v3
du_terminal'45'drop_1456 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_terminal'45'drop_1456 v0 v1 v2
  = if coe v2
      then coe
             MAlonzo.Code.Once.IR.C__'8728'__28 v0
             (coe MAlonzo.Code.Once.IR.C_terminal_72) v1
      else coe MAlonzo.Code.Once.IR.C_terminal_72
-- Once.Optimize.compose-aux
d_compose'45'aux_1472 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  T_ComposeFirstView_70 -> MAlonzo.Code.Once.IR.T_IR_16
d_compose'45'aux_1472 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_cf'45'id_74 -> coe v4
      C_cf'45'terminal_78
        -> coe
             du_terminal'45'drop_1456 (coe v1) (coe v4)
             (coe d_has'45'effect'63'_824 (coe v0) (coe v1) (coe v4))
      C_cf'45'fst_84
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'fst_986 (coe v0) (coe v2) (coe v9) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'snd_90
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe d_optimize'45'snd_1100 (coe v0) (coe v8) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'case_102
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.IR.C_case_68 v16 v17
                      -> coe
                           du_optimize'45'post'45'case_1212 (coe v11) (coe v12) (coe v16)
                           (coe v17) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'comp_114
        -> case coe v3 of
             MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28 v12 v14
                    (coe MAlonzo.Code.Once.IR.C__'8728'__28 v1 v15 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'apply_120
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v11 v12 v13
                      -> coe
                           d_optimize'45'apply_1446 (coe v12) (coe v0) (coe v11) (coe v2)
                           (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cf'45'other_128
        -> coe
             du_optimize'45'compose'45'second_870 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-compose
d_optimize'45'compose_1506 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'compose_1506 v0 v1 v2 v3 v4
  = coe
      d_compose'45'aux_1472 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe du_composeFirstView_560 (coe v3))
-- Once.Optimize.unit-like-aux
d_unit'45'like'45'aux_1516 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Bool
d_unit'45'like'45'aux_1516 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d_not_22
                       (coe d_has'45'effect'63'_824 (coe v0) (coe v1) (coe v2)))
             else coe seq (coe v5) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.unit-like
d_unit'45'like_1526 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_unit'45'like_1526 v0 v1 v2
  = coe
      d_unit'45'like'45'aux_1516 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206 (coe v1)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
-- Once.Optimize.void-like
d_void'45'like_1536 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool
d_void'45'like_1536 v0 ~v1 ~v2 = du_void'45'like_1536 v0
du_void'45'like_1536 :: MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Bool
du_void'45'like_1536 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206 (coe v0)
         (coe MAlonzo.Code.Once.IRTy.C_Void_18))
-- Once.Optimize.fst-like-aux
d_fst'45'like'45'aux_1546 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_184 -> Bool
d_fst'45'like'45'aux_1546 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_190 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'snd_196
        -> coe
             d_unit'45'like_1526
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_snd_48)
      C_fsv'45'other_204
        -> coe
             d_unit'45'like_1526
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v0)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.snd-like-aux
d_snd'45'like'45'aux_1560 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_FstSndView_184 -> Bool
d_snd'45'like'45'aux_1560 v0 v1 v2 v3
  = case coe v3 of
      C_fsv'45'fst_190
        -> coe
             d_unit'45'like_1526
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v0)) (coe v0)
             (coe MAlonzo.Code.Once.IR.C_fst_42)
      C_fsv'45'snd_196 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_fsv'45'other_204
        -> coe
             d_unit'45'like_1526
             (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)) (coe v1)
             (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inl-like-aux
d_inl'45'like'45'aux_1574 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_210 -> Bool
d_inl'45'like'45'aux_1574 v0 ~v1 ~v2 v3
  = du_inl'45'like'45'aux_1574 v0 v3
du_inl'45'like'45'aux_1574 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_210 -> Bool
du_inl'45'like'45'aux_1574 v0 v1
  = case coe v1 of
      C_iiv'45'inl_216 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'inr_222 -> coe du_void'45'like_1536 (coe v0)
      C_iiv'45'other_230 -> coe du_void'45'like_1536 (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.inr-like-aux
d_inr'45'like'45'aux_1588 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_InlInrView_210 -> Bool
d_inr'45'like'45'aux_1588 v0 v1 ~v2 v3
  = du_inr'45'like'45'aux_1588 v0 v1 v3
du_inr'45'like'45'aux_1588 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> T_InlInrView_210 -> Bool
du_inr'45'like'45'aux_1588 v0 v1 v2
  = case coe v2 of
      C_iiv'45'inl_216 -> coe du_void'45'like_1536 (coe v0)
      C_iiv'45'inr_222 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_iiv'45'other_230 -> coe du_void'45'like_1536 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.eta-pair
d_eta'45'pair_1604 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'pair_1604 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'pair_1604 v2 v3 v4 v5
du_eta'45'pair_1604 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'pair_1604 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
      else coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v0 v1
-- Once.Optimize.pair-aux
d_pair'45'aux_1624 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_pair'45'aux_1624 v0 v1 ~v2 v3 v4 v5
  = du_pair'45'aux_1624 v0 v1 v3 v4 v5
du_pair'45'aux_1624 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_pair'45'aux_1624 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'pair_1604 (coe v2) (coe v3)
                       (coe
                          d_fst'45'like'45'aux_1546 (coe v0) (coe v1) (coe v2)
                          (coe du_fstSndView_730 (coe v2)))
                       (coe
                          d_snd'45'like'45'aux_1560 (coe v0) (coe v1) (coe v3)
                          (coe du_fstSndView_730 (coe v3))))
             else coe
                    seq (coe v6)
                    (coe MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-pair
d_optimize'45'pair_1640 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'pair_1640 v0 v1 v2 v3 v4
  = coe
      du_pair'45'aux_1624 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
-- Once.Optimize.eta-case
d_eta'45'case_1660 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
d_eta'45'case_1660 ~v0 ~v1 v2 v3 v4 v5
  = du_eta'45'case_1660 v2 v3 v4 v5
du_eta'45'case_1660 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> Bool -> MAlonzo.Code.Once.IR.T_IR_16
du_eta'45'case_1660 v0 v1 v2 v3
  = if coe v2
      then if coe v3
             then coe MAlonzo.Code.Once.IR.C_id_20
             else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
      else coe MAlonzo.Code.Once.IR.C_case_68 v0 v1
-- Once.Optimize.case-aux
d_case'45'aux_1680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_case'45'aux_1680 v0 v1 ~v2 v3 v4 v5
  = du_case'45'aux_1680 v0 v1 v3 v4 v5
du_case'45'aux_1680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_case'45'aux_1680 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       du_eta'45'case_1660 (coe v2) (coe v3)
                       (coe
                          du_inl'45'like'45'aux_1574 (coe v0)
                          (coe du_inlInrView_778 (coe v2)))
                       (coe
                          du_inr'45'like'45'aux_1588 (coe v0) (coe v1)
                          (coe du_inlInrView_778 (coe v3))))
             else coe seq (coe v6) (coe MAlonzo.Code.Once.IR.C_case_68 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-case
d_optimize'45'case_1696 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'case_1696 v0 v1 v2 v3 v4
  = coe
      du_case'45'aux_1680 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206 (coe v2)
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v0) (coe v1)))
-- Once.Optimize.optimize-once-structural
d_optimize'45'once'45'structural_1712 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once'45'structural_1712 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             d_optimize'45'compose_1506 (coe v0) (coe v4) (coe v1)
             (coe d_optimize'45'once_1718 (coe v4) (coe v1) (coe v6))
             (coe d_optimize'45'once_1718 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    d_optimize'45'pair_1640 (coe v8) (coe v9) (coe v0)
                    (coe d_optimize'45'once_1718 (coe v0) (coe v8) (coe v6))
                    (coe d_optimize'45'once_1718 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.IR.C_snd_48 -> coe MAlonzo.Code.Once.IR.C_snd_48
      MAlonzo.Code.Once.IR.C_inl_54 -> coe MAlonzo.Code.Once.IR.C_inl_54
      MAlonzo.Code.Once.IR.C_inr_60 -> coe MAlonzo.Code.Once.IR.C_inr_60
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    d_optimize'45'case_1696 (coe v8) (coe v9) (coe v1)
                    (coe d_optimize'45'once_1718 (coe v8) (coe v1) (coe v6))
                    (coe d_optimize'45'once_1718 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Once.IR.C_initial_76
      MAlonzo.Code.Once.IR.C_curry_86 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (d_optimize'45'once_1718
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v8))
                       (coe v10) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe MAlonzo.Code.Once.IR.C_apply_94
      MAlonzo.Code.Once.IR.C_In_98 v4
        -> coe MAlonzo.Code.Once.IR.C_In_98 v4
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v4
        -> coe MAlonzo.Code.Once.IR.C_out'45'μ_102 v4
      MAlonzo.Code.Once.IR.C_Cata_110 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Cata_110 v4
                           (d_optimize'45'once_1718
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v10)
                                    (coe v1)))
                              (coe v1) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v4
        -> coe MAlonzo.Code.Once.IR.C_Out_114 v4
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v4
        -> coe MAlonzo.Code.Once.IR.C_in'45'ν_118 v4
      MAlonzo.Code.Once.IR.C_Ana_126 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           MAlonzo.Code.Once.IR.C_Ana_126 v4
                           (d_optimize'45'once_1718
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v10) (coe v9))
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    MAlonzo.Code.Once.IR.C_Iter_134
                    (d_optimize'45'once_1718
                       (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v8))
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v4 v5
        -> coe MAlonzo.Code.Once.IR.C_const_138 v4 v5
      MAlonzo.Code.Once.IR.C_SigOp_144 v3 v4 v5
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
      MAlonzo.Code.Once.IR.C_Call_150 v5
        -> coe MAlonzo.Code.Once.IR.C_Call_150 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Optimize.optimize-once
d_optimize'45'once_1718 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'once_1718 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_212
              (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 erased
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                      (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v1)))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe
                       eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v1))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_irtyTag_204
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                       (coe
                          eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v1))
                          (coe
                             MAlonzo.Code.Once.IRTy.d_irtyTag_204
                             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (let v6
                              = d_has'45'effect'63'_824
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2) in
                        coe
                          (if coe v6
                             then coe
                                    d_optimize'45'once'45'structural_1712 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v2)
                             else coe MAlonzo.Code.Once.IR.C_terminal_72))
                else coe
                       seq (coe v5)
                       (let v6
                              = MAlonzo.Code.Once.IRTy.d_'8799'IRTy'45'aux_212
                                  (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v6 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_irtyTag_204
                                              (coe MAlonzo.Code.Once.IRTy.C_Void_18)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt
                                              (coe MAlonzo.Code.Once.IRTy.d_irtyTag_204 (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_irtyTag_204
                                                 (coe MAlonzo.Code.Once.IRTy.C_Void_18)))))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe seq (coe v8) (coe MAlonzo.Code.Once.IR.C_initial_76)
                                    else coe
                                           seq (coe v8)
                                           (coe
                                              d_optimize'45'once'45'structural_1712 (coe v0)
                                              (coe v1) (coe v2))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Optimize.optimize-n
d_optimize'45'n_1836 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize'45'n_1836 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_optimize'45'n_1836 (coe v0) (coe v1) (coe v4)
                (coe d_optimize'45'once_1718 (coe v0) (coe v1) (coe v3)))
-- Once.Optimize.optimize
d_optimize_1848 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_optimize_1848 v0 v1
  = coe d_optimize'45'n_1836 (coe v0) (coe v1) (coe (10 :: Integer))
