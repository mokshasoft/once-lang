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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatComposition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fetch
d_fetch_62 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
d_fetch_62 ~v0 = du_fetch_62
du_fetch_62 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188
du_fetch_62 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_216
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-go
d_fl'45'go_76 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'go_76 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_116 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.fl-label-match
d_fl'45'label'45'match_80 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_fl'45'label'45'match_80 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_118
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.ft-go
d_ft'45'go_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_ft'45'go_100 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_168 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.ft-match
d_ft'45'match_102 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer -> Maybe Integer
d_ft'45'match_102 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_170 (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-len
d_x86'45'len_156 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
d_x86'45'len_156 ~v0 v1 = du_x86'45'len_156 v1
du_x86'45'len_156 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  Integer
du_x86'45'len_156 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'abstract_14
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off
d_x86'45'off_160 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer
d_x86'45'off_160 ~v0 v1 v2 = du_x86'45'off_160 v1 v2
du_x86'45'off_160 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> Integer
du_x86'45'off_160 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                [] -> coe (0 :: Integer)
                (:) v3 v4
                  -> coe
                       addInt (coe du_x86'45'off_160 (coe v4) (coe v2))
                       (coe du_x86'45'len_156 (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.has-label
d_has'45'label_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
d_has'45'label_168 ~v0 v1 = du_has'45'label_168 v1
du_has'45'label_168 ::
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] -> Bool
du_has'45'label_168 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v1 v2
        -> let v3 = coe du_has'45'label_168 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_label_64 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip
d_find'45'label'45'go'45'skip_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip_180 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-go-skip-other
d_find'45'label'45'go'45'skip'45'other_374 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'go'45'skip'45'other_374 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.HeadView
d_HeadView_392 a0 a1 = ()
data T_HeadView_392
  = C_hv'45'clabel_410 Integer | C_hv'45'plain_424 |
    C_hv'45'otherlabel_442 Integer
                           [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28]
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.reg-op-no-label
d_reg'45'op'45'no'45'label_446 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_RegOp_448 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reg'45'op'45'no'45'label_446 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.const-no-label
d_const'45'no'45'label_454 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_const'45'no'45'label_454 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.headView
d_headView_462 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_HeadView_392
d_headView_462 ~v0 v1 = du_headView_462 v1
du_headView_462 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  T_HeadView_392
du_headView_462 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2190
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2192
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'output'45'to'45'input2_2194
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'input2'45'to'45'output_2196
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2198
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2200
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2202 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2204 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2206
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2208
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2210 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2212 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2214 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2216 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2218 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2220 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2222
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2224
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2226 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2228 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2230 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2232 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2238 v1 v2 v3
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2242 v1 v2 v3
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2244 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2246
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2248 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2250 v1 v2
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2252 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'loop_2254 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2256 v1
        -> coe C_hv'45'plain_424
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2258 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2176 v2
               -> coe C_hv'45'clabel_410 v2
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2178 v2
               -> coe C_hv'45'plain_424
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2180 v2
               -> coe C_hv'45'plain_424
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2182 v2
               -> coe C_hv'45'plain_424
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'thunk_2184 v2 v3
               -> coe
                    C_hv'45'otherlabel_442 v2
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_sub_36
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_22
                             (coe MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.C_rsp_24))
                          (coe
                             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_26
                             (coe
                                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slots_82
                                (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2186 v2
               -> coe C_hv'45'plain_424
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'indexed_2260 v1
        -> coe C_hv'45'plain_424
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-thunk-pres
d_find'45'thunk'45'pres_958 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'thunk'45'pres_958 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'thunk'45'pres_958 v1 v2 v6
du_find'45'thunk'45'pres_958 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'thunk'45'pres_958 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_410 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'thunk'45'pres_958 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'plain_424
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'thunk'45'pres_958 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'otherlabel_442 v9 v10
                      -> let v15 = eqInt (coe v9) (coe v1) in
                         coe
                           (if coe v15
                              then coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                              else coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        addInt (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              du_find'45'thunk'45'pres_958 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.jinj
d_jinj_1090 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jinj_1090 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_1092 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_1092 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_1096 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_1096 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.just-inj
d_just'45'inj_1152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_1152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-pres
d_find'45'label'45'pres_1166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find'45'label'45'pres_1166 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_find'45'label'45'pres_1166 v1 v2 v6
du_find'45'label'45'pres_1166 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find'45'label'45'pres_1166 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v7 of
                    C_hv'45'clabel_410 v9
                      -> let v13 = eqInt (coe v9) (coe v1) in
                         coe
                           (if coe v13
                              then coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                              else coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        addInt (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              du_find'45'label'45'pres_1166 (coe v4) (coe v1)
                                              (coe v8))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    C_hv'45'plain_424
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_1166 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    C_hv'45'otherlabel_442 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              addInt (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe du_find'45'label'45'pres_1166 (coe v4) (coe v1) (coe v8))))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.acc≡j
d_acc'8801'j_1290 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_acc'8801'j_1290 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.comp1
d_comp1_1294 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comp1_1294 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.all-headView
d_all'45'headView_1344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'headView_1344 ~v0 v1 = du_all'45'headView_1344 v1
du_all'45'headView_1344 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'headView_1344 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_headView_462 (coe v1))
             (coe du_all'45'headView_1344 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-corr
d_find'45'label'45'corr_1358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'corr_1358 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-thunk-corr
d_find'45'thunk'45'corr_1402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'thunk'45'corr_1402 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-len-++
d_drop'45'len'45''43''43'_1444 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'len'45''43''43'_1444 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-[]
d_drop'45''91''93'_1458 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_1458 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-+
d_drop'45''43'_1470 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''43'_1470 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-compile
d_drop'45'compile_1492 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'compile_1492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-drop
d_fetch'45'drop_1508 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_28] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'drop_1508 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-at-offset
d_fetch'45'at'45'offset_1528 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'at'45'offset_1528 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.x86-off-suc
d_x86'45'off'45'suc_1542 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'off'45'suc_1542 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.drop-fetch
d_drop'45'fetch_1570 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'fetch_1570 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-head
d_fetch'45'block'45'head_1596 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'head_1596 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-2nd
d_fetch'45'block'45'2nd_1614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'2nd_1614 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-3rd
d_fetch'45'block'45'3rd_1634 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'3rd_1634 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-4th
d_fetch'45'block'45'4th_1654 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'4th_1654 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-5th
d_fetch'45'block'45'5th_1674 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'5th_1674 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.fetch-block-6th
d_fetch'45'block'45'6th_1694 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'block'45'6th_1694 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-go
d_find'45'label'45'none'45'go_1716 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'go_1716 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition._.absurd
d_absurd_1824 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
   Integer ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_absurd_1824 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatComposition.find-label-none-corr
d_find'45'label'45'none'45'corr_1862 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2188] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_find'45'label'45'none'45'corr_1862 = erased
