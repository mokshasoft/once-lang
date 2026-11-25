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

module MAlonzo.Code.Once.CCC.Codegen.StackDepth where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.Compile
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.CCC.Codegen.AllocExpand
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.CCC.Codegen.StackDepth.block-scratch
d_block'45'scratch_12 ::
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
d_block'45'scratch_12 ~v0 v1 v2 = du_block'45'scratch_12 v1 v2
du_block'45'scratch_12 ::
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 -> Integer
du_block'45'scratch_12 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Type.C_NInt_8
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
             (coe
                MAlonzo.Code.Once.Arith.Machine.Compile.du_normalize_322 (coe v1))
      MAlonzo.Code.Once.Arith.Type.C_NFloat_10
        -> coe
             MAlonzo.Code.Once.Arith.Machine.Compile.du_required'45'scratch_14
             (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.sigop-call-words
d_sigop'45'call'45'words_18 :: Integer
d_sigop'45'call'45'words_18 = coe (5 :: Integer)
-- Once.CCC.Codegen.StackDepth.sigop-scratch
d_sigop'45'scratch_24 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Integer
d_sigop'45'scratch_24 ~v0 ~v1 v2 = du_sigop'45'scratch_24 v2
du_sigop'45'scratch_24 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 -> Integer
du_sigop'45'scratch_24 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.SigOp.Info.C_blockV_86 v2 v3 v4
           -> coe du_block'45'scratch_12 (coe v3) (coe v4)
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepth.sigop-need
d_sigop'45'need_32 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 -> Integer
d_sigop'45'need_32 ~v0 ~v1 v2 = du_sigop'45'need_32 v2
du_sigop'45'need_32 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 -> Integer
du_sigop'45'need_32 v0
  = coe
      addInt
      (coe
         du_sigop'45'scratch_24
         (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v0)))
      (coe d_sigop'45'call'45'words_18)
-- Once.CCC.Codegen.StackDepth.Owner
d_Owner_36 = ()
data T_Owner_36
  = C_o'45'start_38 |
    C_o'45'entry_40 MAlonzo.Code.Once.CCC.Label.T_EntryId_22
-- Once.CCC.Codegen.StackDepth._≡ᵇᴼ_
d__'8801''7495''7484'__42 :: T_Owner_36 -> T_Owner_36 -> Bool
d__'8801''7495''7484'__42 v0 v1
  = case coe v0 of
      C_o'45'start_38
        -> case coe v1 of
             C_o'45'start_38 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_o'45'entry_40 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_o'45'entry_40 v2
        -> case coe v1 of
             C_o'45'start_38 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_o'45'entry_40 v3
               -> coe
                    MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7473'__136 (coe v2)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.≡ᵇᴼ-true
d_'8801''7495''7484''45'true_52 ::
  T_Owner_36 ->
  T_Owner_36 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''7484''45'true_52 = erased
-- Once.CCC.Codegen.StackDepth.Kind
d_Kind_60 = ()
data T_Kind_60
  = C_k'45'call_62 MAlonzo.Code.Once.CCC.Label.T_EntryId_22 |
    C_k'45'clo_64 | C_k'45'sig_66 Integer |
    C_k'45'entry_68 MAlonzo.Code.Once.CCC.Label.T_EntryId_22 Integer |
    C_k'45'label_70 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_k'45'jump_72 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_k'45'branch_74 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_k'45'ret_76 | C_k'45'start_78 | C_k'45'none_80
-- Once.CCC.Codegen.StackDepth.kind
d_kind_82 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  T_Kind_60
d_kind_82 v0
  = let v1 = coe C_k'45'none_80 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2462
           -> coe C_k'45'clo_64
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2476 v2 v3 v4
           -> coe C_k'45'sig_66 (coe du_sigop'45'need_32 (coe v4))
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v3
                  -> coe C_k'45'label_70 (coe v3)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v3
                  -> coe C_k'45'jump_72 (coe v3)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v3
                  -> coe C_k'45'branch_74 (coe v3)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v3 v4
                  -> coe C_k'45'entry_68 (coe v3) (coe v4)
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v3
                  -> coe C_k'45'ret_76
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v3
                  -> coe
                       C_k'45'call_62
                       (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v3))
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v3
                  -> coe C_k'45'start_78
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
                  -> coe C_k'45'ret_76
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepth.own-k
d_own'45'k_98 :: T_Owner_36 -> T_Kind_60 -> T_Owner_36
d_own'45'k_98 v0 v1
  = case coe v1 of
      C_k'45'call_62 v2 -> coe v0
      C_k'45'clo_64 -> coe v0
      C_k'45'sig_66 v2 -> coe v0
      C_k'45'entry_68 v2 v3 -> coe C_o'45'entry_40 (coe v2)
      C_k'45'label_70 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Once.CCC.Label.d__'8801''7495''7477'__58 (coe v2)
                (coe
                   MAlonzo.Code.Once.CCC.Codegen.AllocExpand.d_skip'45'label_154))
             (coe C_o'45'start_38) (coe v0)
      C_k'45'jump_72 v2 -> coe v0
      C_k'45'branch_74 v2 -> coe v0
      C_k'45'ret_76 -> coe v0
      C_k'45'start_78 -> coe v0
      C_k'45'none_80 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.own
d_own_124 ::
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  T_Owner_36
d_own_124 v0 v1
  = coe d_own'45'k_98 (coe v0) (coe d_kind_82 (coe v1))
-- Once.CCC.Codegen.StackDepth.entry-k
d_entry'45'k_130 :: T_Kind_60 -> Bool
d_entry'45'k_130 v0
  = case coe v0 of
      C_k'45'call_62 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'clo_64 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'sig_66 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'entry_68 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_k'45'label_70 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'jump_72 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'branch_74 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'ret_76 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'start_78 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_k'45'none_80 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.frame-k
d_frame'45'k_132 :: T_Kind_60 -> Integer
d_frame'45'k_132 v0
  = case coe v0 of
      C_k'45'call_62 v1 -> coe (0 :: Integer)
      C_k'45'clo_64 -> coe (0 :: Integer)
      C_k'45'sig_66 v1 -> coe (0 :: Integer)
      C_k'45'entry_68 v1 v2 -> coe v2
      C_k'45'label_70 v1 -> coe (0 :: Integer)
      C_k'45'jump_72 v1 -> coe (0 :: Integer)
      C_k'45'branch_74 v1 -> coe (0 :: Integer)
      C_k'45'ret_76 -> coe (0 :: Integer)
      C_k'45'start_78 -> coe (0 :: Integer)
      C_k'45'none_80 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.falls-k
d_falls'45'k_136 :: T_Kind_60 -> Bool
d_falls'45'k_136 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v0 of
         C_k'45'jump_72 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         C_k'45'ret_76 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> coe v1)
-- Once.CCC.Codegen.StackDepth.frame-other
d_frame'45'other_140 ::
  T_Kind_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frame'45'other_140 = erased
-- Once.CCC.Codegen.StackDepth.before-from
d_before'45'from_142 ::
  T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> T_Owner_36
d_before'45'from_142 v0 v1 v2
  = case coe v1 of
      [] -> coe v0
      (:) v3 v4
        -> case coe v2 of
             0 -> coe v0
             _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_before'45'from_142 (coe d_own_124 (coe v0) (coe v3)) (coe v4)
                       (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.owner-from
d_owner'45'from_160 ::
  T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> T_Owner_36
d_owner'45'from_160 v0 v1 v2
  = case coe v1 of
      [] -> coe v0
      (:) v3 v4
        -> case coe v2 of
             0 -> coe d_own_124 (coe v0) (coe v3)
             _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d_owner'45'from_160 (coe d_own_124 (coe v0) (coe v3)) (coe v4)
                       (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.owner
d_owner_178 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> T_Owner_36
d_owner_178 = coe d_owner'45'from_160 (coe C_o'45'start_38)
-- Once.CCC.Codegen.StackDepth.at
d_at_180 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430
d_at_180 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe (coe d_at_180 (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.owner-from-suc
d_owner'45'from'45'suc_196 ::
  T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_owner'45'from'45'suc_196 = erased
-- Once.CCC.Codegen.StackDepth.owner-from-end
d_owner'45'from'45'end_226 ::
  T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_owner'45'from'45'end_226 = erased
-- Once.CCC.Codegen.StackDepth.Depths
d_Depths_254 = ()
data T_Depths_254
  = C_depths_288 (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Bool)
                 (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer)
                 (MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer) Integer
                 (T_Owner_36 -> Bool) Integer Bool
                 (MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Owner_36)
-- Once.CCC.Codegen.StackDepth.Depths.bnd
d_bnd_272 ::
  T_Depths_254 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Bool
d_bnd_272 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.dep
d_dep_274 ::
  T_Depths_254 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer
d_dep_274 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.past
d_past_276 ::
  T_Depths_254 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Integer
d_past_276 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.past₀
d_past'8320'_278 :: T_Depths_254 -> Integer
d_past'8320'_278 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.clo-chk
d_clo'45'chk_280 :: T_Depths_254 -> T_Owner_36 -> Bool
d_clo'45'chk_280 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.clo-dep
d_clo'45'dep_282 :: T_Depths_254 -> Integer
d_clo'45'dep_282 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.sig-chk
d_sig'45'chk_284 :: T_Depths_254 -> Bool
d_sig'45'chk_284 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Depths.lown
d_lown_286 ::
  T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> T_Owner_36
d_lown_286 v0
  = case coe v0 of
      C_depths_288 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.pastO
d_pastO_290 :: T_Depths_254 -> T_Owner_36 -> Integer
d_pastO_290 v0 v1
  = case coe v1 of
      C_o'45'start_38 -> coe d_past'8320'_278 (coe v0)
      C_o'45'entry_40 v2 -> coe d_past_276 v0 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.chk
d_chk_298 ::
  T_Depths_254 ->
  T_Owner_36 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Bool
d_chk_298 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8744'__30
      (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_bnd_272 v0 v2))
      (coe
         d__'8801''7495''7484'__42 (coe v1) (coe C_o'45'entry_40 (coe v2)))
-- Once.CCC.Codegen.StackDepth.cost-k
d_cost'45'k_306 ::
  T_Depths_254 -> T_Owner_36 -> T_Kind_60 -> Integer
d_cost'45'k_306 v0 v1 v2
  = case coe v2 of
      C_k'45'call_62 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_chk_298 (coe v0) (coe v1) (coe v3)) (coe (0 :: Integer))
             (coe addInt (coe (1 :: Integer)) (coe d_dep_274 v0 v3))
      C_k'45'clo_64
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_clo'45'chk_280 v0 v1) (coe (0 :: Integer))
             (coe addInt (coe (1 :: Integer)) (coe d_clo'45'dep_282 (coe v0)))
      C_k'45'sig_66 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe d_sig'45'chk_284 (coe v0)) (coe (0 :: Integer)) (coe v3)
      C_k'45'entry_68 v3 v4 -> coe (0 :: Integer)
      C_k'45'label_70 v3 -> coe (0 :: Integer)
      C_k'45'jump_72 v3 -> coe (0 :: Integer)
      C_k'45'branch_74 v3 -> coe (0 :: Integer)
      C_k'45'ret_76 -> coe (0 :: Integer)
      C_k'45'start_78 -> coe (0 :: Integer)
      C_k'45'none_80 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.cost
d_cost_352 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  Integer
d_cost_352 v0 v1 v2
  = coe d_cost'45'k_306 (coe v0) (coe v1) (coe d_kind_82 (coe v2))
-- Once.CCC.Codegen.StackDepth.thunk-ok
d_thunk'45'ok_360 ::
  T_Depths_254 -> MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> Bool
d_thunk'45'ok_360 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe d_dep_274 v0 v1) (coe d_clo'45'dep_282 (coe v0))
      MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v2
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.extra-k
d_extra'45'k_368 :: T_Depths_254 -> T_Owner_36 -> T_Kind_60 -> Bool
d_extra'45'k_368 v0 v1 v2
  = case coe v2 of
      C_k'45'call_62 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_k'45'clo_64 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_k'45'sig_66 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_k'45'entry_68 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                (coe addInt (coe d_past_276 v0 v3) (coe v4)) (coe d_dep_274 v0 v3))
             (coe d_thunk'45'ok_360 (coe v0) (coe v3))
      C_k'45'label_70 v3
        -> coe d__'8801''7495''7484'__42 (coe d_lown_286 v0 v3) (coe v1)
      C_k'45'jump_72 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe d_pastO_290 (coe v0) (coe d_lown_286 v0 v3))
             (coe d_pastO_290 (coe v0) (coe v1))
      C_k'45'branch_74 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe d_pastO_290 (coe v0) (coe d_lown_286 v0 v3))
             (coe d_pastO_290 (coe v0) (coe v1))
      C_k'45'ret_76 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      C_k'45'start_78
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe d_pastO_290 (coe v0) (coe v1))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_start'45'stack'45'words_2416)
      C_k'45'none_80 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.ok-at
d_ok'45'at_420 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 -> Bool
d_ok'45'at_420 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
         (coe d_cost_352 (coe v0) (coe v1) (coe v2))
         (coe d_pastO_290 (coe v0) (coe v1)))
      (coe d_extra'45'k_368 (coe v0) (coe v1) (coe d_kind_82 (coe v2)))
-- Once.CCC.Codegen.StackDepth.fall-ok
d_fall'45'ok_428 ::
  T_Depths_254 -> T_Owner_36 -> Bool -> T_Owner_36 -> Bool
d_fall'45'ok_428 v0 v1 v2 v3
  = if coe v2
      then coe
             MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
             (coe d_pastO_290 (coe v0) (coe v3))
             (coe d_pastO_290 (coe v0) (coe v1))
      else coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
-- Once.CCC.Codegen.StackDepth.consistent-from
d_consistent'45'from_442 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] -> Bool
d_consistent'45'from_442 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
             (coe
                d_ok'45'at_420 (coe v0) (coe d_own_124 (coe v1) (coe v4)) (coe v4))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe
                   d_fall'45'ok_428 (coe v0) (coe v1) (coe v2)
                   (coe d_own_124 (coe v1) (coe v4)))
                (coe
                   d_consistent'45'from_442 (coe v0) (coe d_own_124 (coe v1) (coe v4))
                   (coe d_falls'45'k_136 (coe d_kind_82 (coe v4))) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.consistent?
d_consistent'63'_460 ::
  T_Depths_254 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] -> Bool
d_consistent'63'_460 v0 v1
  = coe
      d_consistent'45'from_442 (coe v0) (coe C_o'45'start_38)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1)
-- Once.CCC.Codegen.StackDepth.jumps-k
d_jumps'45'k_466 ::
  T_Kind_60 -> MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> ()
d_jumps'45'k_466 = erased
-- Once.CCC.Codegen.StackDepth.jumps-to
d_jumps'45'to_478 ::
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> ()
d_jumps'45'to_478 = erased
-- Once.CCC.Codegen.StackDepth.jumps-not-entry
d_jumps'45'not'45'entry_490 ::
  T_Kind_60 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_jumps'45'not'45'entry_490 = erased
-- Once.CCC.Codegen.StackDepth.Cert
d_Cert_500 a0 a1 = ()
data T_Cert_500
  = C_constructor_594 (Integer ->
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
                       Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                       Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       Integer ->
                       MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
                       AgdaAny ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       Integer ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
                      (Integer ->
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
                       MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- Once.CCC.Codegen.StackDepth.Cert.cost-le
d_cost'45'le_554 ::
  T_Cert_500 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_cost'45'le_554 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Cert.dep-le
d_dep'45'le_562 ::
  T_Cert_500 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dep'45'le_562 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Cert.clo-le
d_clo'45'le_570 ::
  T_Cert_500 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_clo'45'le_570 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Cert.jump-le
d_jump'45'le_578 ::
  T_Cert_500 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_jump'45'le_578 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Cert.start-le
d_start'45'le_584 ::
  T_Cert_500 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_start'45'le_584 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.Cert.fall-le
d_fall'45'le_592 ::
  T_Cert_500 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fall'45'le_592 v0
  = case coe v0 of
      C_constructor_594 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.∧-l
d_'8743''45'l_600 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'l_600 = erased
-- Once.CCC.Codegen.StackDepth.∧-r
d_'8743''45'r_606 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'r_606 = erased
-- Once.CCC.Codegen.StackDepth.≤ᵇ-sound
d_'8804''7495''45'sound_614 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''7495''45'sound_614 v0 ~v1 ~v2
  = du_'8804''7495''45'sound_614 v0
du_'8804''7495''45'sound_614 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''7495''45'sound_614 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
      (coe v0)
-- Once.CCC.Codegen.StackDepth.rest-of
d_rest'45'of_632 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rest'45'of_632 = erased
-- Once.CCC.Codegen.StackDepth.ok-of
d_ok'45'of_658 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ok'45'of_658 = erased
-- Once.CCC.Codegen.StackDepth.fall-of
d_fall'45'of_706 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_fall'45'of_706 v0 v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_fall'45'of_706 v0 v1 v3 v5
du_fall'45'of_706 ::
  T_Depths_254 ->
  T_Owner_36 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_fall'45'of_706 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> case coe v3 of
             0 -> coe
                    seq (coe v5)
                    (coe
                       du_'8804''7495''45'sound_614
                       (coe
                          d_pastO_290 (coe v0)
                          (coe d_owner'45'from_160 (coe v1) (coe v2) (coe (1 :: Integer)))))
             _ -> let v6 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_fall'45'of_706 (coe v0) (coe d_own_124 (coe v1) (coe v4))
                       (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.extra-of
d_extra'45'of_760 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extra'45'of_760 = erased
-- Once.CCC.Codegen.StackDepth.label-owner
d_label'45'owner_812 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_label'45'owner_812 = erased
-- Once.CCC.Codegen.StackDepth.jump-k
d_jump'45'k_830 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  T_Kind_60 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_jump'45'k_830 v0 ~v1 v2 v3 ~v4 ~v5 = du_jump'45'k_830 v0 v2 v3
du_jump'45'k_830 ::
  T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  T_Kind_60 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_jump'45'k_830 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         du_'8804''7495''45'sound_614
         (coe d_pastO_290 (coe v0) (coe d_lown_286 v0 v1)))
-- Once.CCC.Codegen.StackDepth.jump-at
d_jump'45'at_864 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_jump'45'at_864 v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7
  = du_jump'45'at_864 v0 v3 v4 v5
du_jump'45'at_864 ::
  T_Depths_254 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_jump'45'at_864 v0 v1 v2 v3
  = coe du_go_888 (coe v0) (coe v3) (coe d_at_180 (coe v1) (coe v2))
-- Once.CCC.Codegen.StackDepth._.go
d_go_888 ::
  T_Depths_254 ->
  T_Owner_36 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_go_888 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du_go_888 v0 v5 v8
du_go_888 ::
  T_Depths_254 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_go_888 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_jump'45'k_830 (coe v0) (coe v1) (coe d_kind_82 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.StackDepth.entry-ok
d_entry'45'ok_904 ::
  T_Depths_254 ->
  T_Owner_36 ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_entry'45'ok_904 ~v0 ~v1 ~v2 ~v3 ~v4 = du_entry'45'ok_904
du_entry'45'ok_904 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_entry'45'ok_904
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.CCC.Codegen.StackDepth.cert-of
d_cert'45'of_920 ::
  T_Depths_254 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Cert_500
d_cert'45'of_920 v0 v1 ~v2 = du_cert'45'of_920 v0 v1
du_cert'45'of_920 ::
  T_Depths_254 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  T_Cert_500
du_cert'45'of_920 v0 v1
  = coe
      C_constructor_594
      (coe
         (\ v2 v3 v4 ->
            coe
              du_'8804''7495''45'sound_614
              (coe d_cost_352 (coe v0) (coe d_owner_178 v1 v2) (coe v3))))
      (coe
         (\ v2 v3 v4 v5 ->
            coe
              du_'8804''7495''45'sound_614
              (coe addInt (coe d_past_276 v0 v3) (coe v4))))
      (coe
         (\ v2 v3 v4 v5 ->
            coe
              du_'8804''7495''45'sound_614
              (coe
                 d_dep_274 v0
                 (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v3)))))
      (coe
         (\ v2 v3 v4 v5 v6 ->
            coe du_jump'45'at_864 (coe v0) (coe v1) (coe v2) (coe v4)))
      (coe
         (\ v2 v3 v4 ->
            coe
              du_'8804''7495''45'sound_614
              (coe d_pastO_290 (coe v0) (coe d_owner_178 v1 v2))))
      (\ v2 v3 v4 v5 v6 v7 ->
         coe du_fall'45'of_706 (coe v0) (coe C_o'45'start_38) (coe v1) v2)
-- Once.CCC.Codegen.StackDepth._.cs
d_cs_932 ::
  T_Depths_254 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cs_932 = erased
-- Once.CCC.Codegen.StackDepth.T₀
d_T'8320'_986 :: Integer -> T_Depths_254
d_T'8320'_986 v0
  = coe
      C_depths_288
      (coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
      (coe (\ v1 -> v0)) (coe (\ v1 -> 0 :: Integer))
      (coe (0 :: Integer))
      (coe (\ v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
      (coe v0) (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe (\ v1 -> coe C_o'45'start_38))
-- Once.CCC.Codegen.StackDepth.cost₀-k
d_cost'8320''45'k_1006 ::
  Integer ->
  T_Owner_36 ->
  T_Kind_60 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cost'8320''45'k_1006 = erased
-- Once.CCC.Codegen.StackDepth.pastO₀
d_pastO'8320'_1056 ::
  Integer ->
  T_Owner_36 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pastO'8320'_1056 = erased
-- Once.CCC.Codegen.StackDepth.cert₀
d_cert'8320'_1072 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_Cert_500
d_cert'8320'_1072 v0 ~v1 v2 = du_cert'8320'_1072 v0 v2
du_cert'8320'_1072 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  T_Cert_500
du_cert'8320'_1072 v0 v1
  = coe
      C_constructor_594
      (coe (\ v2 v3 v4 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe (\ v2 v3 v4 v5 -> coe v1 v2 v3 v4 v5))
      (coe
         (\ v2 v3 v4 v5 ->
            MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
              (coe
                 d_dep_274 (d_T'8320'_986 (coe v0))
                 (coe MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 (coe v3)))))
      (coe
         (\ v2 v3 v4 v5 v6 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe (\ v2 v3 v4 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      (coe
         (\ v2 v3 v4 v5 v6 v7 ->
            coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
