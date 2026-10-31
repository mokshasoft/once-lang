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

module MAlonzo.Code.Once.CCC.Codegen.IRToTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRToTrace.rec-count
d_rec'45'count_10 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
d_rec'45'count_10 ~v0 v1 = du_rec'45'count_10 v1
du_rec'45'count_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
du_rec'45'count_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_rec'45'count_10 (coe v1)) (coe du_rec'45'count_10 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v1 v2
        -> coe
             addInt (coe du_rec'45'count_10 (coe v1))
             (coe du_rec'45'count_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.CataStrategy
d_CataStrategy_20 a0 = ()
data T_CataStrategy_20
  = C_strat'45'const_22 |
    C_strat'45'branching_24 MAlonzo.Code.Once.Internal.Type.T_Functor_6
-- Once.CCC.Codegen.IRToTrace.cata-strategy
d_cata'45'strategy_26 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> T_CataStrategy_20
d_cata'45'strategy_26 ~v0 v1 = du_cata'45'strategy_26 v1
du_cata'45'strategy_26 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> T_CataStrategy_20
du_cata'45'strategy_26 v0
  = let v1 = coe du_rec'45'count_10 (coe v0) in
    coe
      (case coe v1 of
         0 -> coe C_strat'45'const_22
         _ -> coe C_strat'45'branching_24 (coe v0))
-- Once.CCC.Codegen.IRToTrace.cata-body
d_cata'45'body_38 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cata'45'body_38 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
            (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2060
               (coe
                  MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24
                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v1)))
               (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2062 (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v2))))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-call-setup
d_cata'45'call'45'setup_48 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cata'45'call'45'setup_48 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
            (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                  (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                        (coe v1))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130
                                    (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-call
d_cata'45'call_58 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cata'45'call_58 ~v0 v1 v2 v3 v4 = du_cata'45'call_58 v1 v2 v3 v4
du_cata'45'call_58 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_cata'45'call_58 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
            (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
               (coe (2 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                  (coe v3))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                        (coe v2))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                              (coe v1))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                    (coe v0))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2132)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2108)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
-- Once.CCC.Codegen.IRToTrace.fsize
d_fsize_68 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
d_fsize_68 ~v0 v1 = du_fsize_68 v1
du_fsize_68 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
du_fsize_68 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_fsize_68 (coe v1)))
             (coe du_fsize_68 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_fsize_68 (coe v1)))
             (coe du_fsize_68 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.push2
d_push2_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_push2_84 ~v0 v1 v2 v3 = du_push2_84 v1 v2 v3
du_push2_84 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_push2_84 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
               (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                     (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                           (coe v0))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                    (coe v0))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.pop2
d_pop2_94 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_pop2_94 ~v0 v1 = du_pop2_94 v1
du_pop2_94 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_pop2_94 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
         (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.wrap-sum
d_wrap'45'sum_102 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_wrap'45'sum_102 ~v0 v1 v2 = du_wrap'45'sum_102 v1 v2
du_wrap'45'sum_102 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_wrap'45'sum_102 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
               (coe addInt (coe (1 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                     (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Once.CCC.Codegen.IRToTrace.lsize
d_lsize_108 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
d_lsize_108 ~v0 v1 = du_lsize_108 v1
du_lsize_108 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> Integer
du_lsize_108 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v1 v2
        -> coe
             addInt
             (coe addInt (coe (2 :: Integer)) (coe du_lsize_108 (coe v1)))
             (coe du_lsize_108 (coe v2))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v1 v2
        -> coe
             addInt (coe du_lsize_108 (coe v1)) (coe du_lsize_108 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.visit-walk
d_visit'45'walk_128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_visit'45'walk_128 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v7
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Internal.Type.C_Id_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
             (coe du_push2_84 (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_visit'45'walk_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe addInt (coe (2 :: Integer)) (coe du_lsize_108 (coe v7)))
                      (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         d_visit'45'walk_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v6)))))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_visit'45'walk_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                   (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      d_visit'45'walk_128 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                      (coe addInt (coe (4 :: Integer)) (coe v5))
                      (coe addInt (coe du_lsize_108 (coe v7)) (coe v6)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.rebuild-walk
d_rebuild'45'walk_188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_rebuild'45'walk_188 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_rebuild'45'walk_188 v0 v1 v4 v5 v6
du_rebuild'45'walk_188 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_rebuild'45'walk_188 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Type.C_K_12 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Internal.Type.C_Id_14 -> coe du_pop2_94 (coe v1)
      MAlonzo.Code.Once.Internal.Type.C__'8853'__16 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_rebuild'45'walk_188 (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe addInt (coe (2 :: Integer)) (coe du_lsize_108 (coe v5)))
                      (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe du_wrap'45'sum_102 (coe (1 :: Integer)) (coe v3))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            du_rebuild'45'walk_188 (coe v0) (coe v1) (coe v5)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe du_wrap'45'sum_102 (coe (0 :: Integer)) (coe v3))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                     (coe
                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                        (coe addInt (coe (1 :: Integer)) (coe v4)))))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
      MAlonzo.Code.Once.Internal.Type.C__'8855'__18 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_rebuild'45'walk_188 (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe addInt (coe du_lsize_108 (coe v5)) (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                         (coe addInt (coe (2 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_188 (coe v0) (coe v1) (coe v5)
                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe addInt (coe (1 :: Integer)) (coe v3)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                  (coe addInt (coe (3 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                              (coe addInt (coe (2 :: Integer)) (coe v3)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                    (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-br-I₁
d_cata'45'br'45'I'8321'_238 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cata'45'br'45'I'8321'_238 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            du_push2_84 (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_push2_84 (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        d_visit'45'walk_128 (coe v0) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 du_rebuild'45'walk_188 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe addInt (coe (4 :: Integer)) (coe du_lsize_108 (coe v1)))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-br-I₂
d_cata'45'br'45'I'8322'_246 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cata'45'br'45'I'8322'_246 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         du_push2_84 (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                     (coe addInt (coe (2 :: Integer)) (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                     (coe
                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                        (coe addInt (coe (3 :: Integer)) (coe v2)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
               (coe addInt (coe (2 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-branching
d_cata'45'trace'45'branching_252 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_252 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            addInt (coe (15 :: Integer))
            (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt
            (coe
               addInt
               (coe addInt (coe (6 :: Integer)) (coe du_lsize_108 (coe v1)))
               (coe du_lsize_108 (coe v1)))
            (coe v4))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_48 (coe v0)
               (coe
                  addInt
                  (coe
                     addInt (coe (11 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt (coe (12 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt (coe (13 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt
                     (coe addInt (coe (4 :: Integer)) (coe du_lsize_108 (coe v1)))
                     (coe du_lsize_108 (coe v1)))
                  (coe v4)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  d_cata'45'br'45'I'8321'_238 (coe v0) (coe v1) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     du_cata'45'call_58
                     (coe
                        addInt
                        (coe
                           addInt (coe (11 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                        (coe v3))
                     (coe
                        addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                        (coe v3))
                     (coe
                        addInt
                        (coe
                           addInt (coe (13 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                        (coe v3))
                     (coe
                        addInt
                        (coe
                           addInt (coe (14 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_68 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe d_cata'45'br'45'I'8322'_246 (coe v0) (coe v3) (coe v4))
                     (coe
                        d_cata'45'body_38 (coe v0)
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (4 :: Integer)) (coe du_lsize_108 (coe v1)))
                              (coe du_lsize_108 (coe v1)))
                           (coe v4))
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (5 :: Integer)) (coe du_lsize_108 (coe v1)))
                              (coe du_lsize_108 (coe v1)))
                           (coe v4))
                        (coe v2) (coe v5)))))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-const
d_cata'45'trace'45'const_264 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (4 :: Integer)) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (2 :: Integer)) (coe v3))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_48 (coe v0) (coe v2)
               (coe addInt (coe (1 :: Integer)) (coe v2))
               (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_cata'45'call_58 (coe v2)
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (2 :: Integer)) (coe v2))
                  (coe addInt (coe (3 :: Integer)) (coe v2)))
               (coe
                  d_cata'45'body_38 (coe v0) (coe v3)
                  (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v1) (coe v4)))))
-- Once.CCC.Codegen.IRToTrace.cata-dispatch
d_cata'45'dispatch_274 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_274 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      C_strat'45'const_22
        -> coe
             d_cata'45'trace'45'const_264 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      C_strat'45'branching_24 v6
        -> coe
             d_cata'45'trace'45'branching_252 (coe v0) (coe v6) (coe v2)
             (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.resuspend-layer
d_resuspend'45'layer_296 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_296 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (4 :: Integer)) (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                      (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                         (coe (2 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe addInt (coe (1 :: Integer)) (coe v1)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                               (coe v4))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                    (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                                       (coe (2 :: Integer)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                          (coe
                                                             addInt (coe (3 :: Integer)) (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                (coe
                                                                   addInt (coe (2 :: Integer))
                                                                   (coe v1)))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130
                                                                      (coe v3))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                            (coe
                                                                               addInt
                                                                               (coe (3 :: Integer))
                                                                               (coe v1)))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_296 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_296 (coe v0)
                                (coe addInt (coe (3 :: Integer)) (coe v1))
                                (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_296 (coe v0)
                                   (coe addInt (coe (3 :: Integer)) (coe v1))
                                   (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                   (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_296 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_296 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1))
                                      (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                      (coe v11) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_296 (coe v0)
                                         (coe addInt (coe (3 :: Integer)) (coe v1))
                                         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                         (coe v4) (coe v11) (coe v9))))
                                (coe v3) (coe v4) (coe v12) (coe v10))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                   (coe v1))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v2))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                      (coe v1))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_resuspend'45'layer_296 (coe v0)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_resuspend'45'layer_296 (coe v0)
                                                  (coe addInt (coe (3 :: Integer)) (coe v1))
                                                  (coe addInt (coe (2 :: Integer)) (coe v2))
                                                  (coe v3) (coe v4) (coe v11) (coe v9)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_resuspend'45'layer_296 (coe v0)
                                                     (coe addInt (coe (3 :: Integer)) (coe v1))
                                                     (coe addInt (coe (2 :: Integer)) (coe v2))
                                                     (coe v3) (coe v4) (coe v11) (coe v9))))
                                            (coe v3) (coe v4) (coe v12) (coe v10))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                         (coe addInt (coe (2 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                            (coe (2 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                               (coe addInt (coe (1 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                     (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                                                           (coe (1 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                 (coe
                                                                    addInt (coe (1 :: Integer))
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe v2))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_resuspend'45'layer_296 (coe v0)
                                                  (coe addInt (coe (3 :: Integer)) (coe v1))
                                                  (coe addInt (coe (2 :: Integer)) (coe v2))
                                                  (coe v3) (coe v4) (coe v11) (coe v9))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                               (coe addInt (coe (2 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                                  (coe (2 :: Integer)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                           (coe
                                                              addInt (coe (2 :: Integer)) (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v1)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_296 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_296 (coe v0)
                                (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                (coe v4) (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_296 (coe v0)
                                   (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                   (coe v4) (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_296 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_296 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                      (coe v4) (coe v11) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_296 (coe v0)
                                         (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                         (coe v3) (coe v4) (coe v11) (coe v9))))
                                (coe v3) (coe v4) (coe v12) (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_resuspend'45'layer_296 (coe v0)
                                            (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                            (coe v3) (coe v4) (coe v11) (coe v9))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                         (coe addInt (coe (2 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                            (coe (2 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                               (coe addInt (coe (1 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                     (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                    (coe
                                                                       d_resuspend'45'layer_296
                                                                       (coe v0)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe
                                                                             d_resuspend'45'layer_296
                                                                             (coe v0)
                                                                             (coe
                                                                                addInt
                                                                                (coe (3 :: Integer))
                                                                                (coe v1))
                                                                             (coe v2) (coe v3)
                                                                             (coe v4) (coe v11)
                                                                             (coe v9)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                             (coe
                                                                                d_resuspend'45'layer_296
                                                                                (coe v0)
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      (3 ::
                                                                                         Integer))
                                                                                   (coe v1))
                                                                                (coe v2) (coe v3)
                                                                                (coe v4) (coe v11)
                                                                                (coe v9))))
                                                                       (coe v3) (coe v4) (coe v12)
                                                                       (coe v10))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                                    (coe
                                                                       addInt (coe (2 :: Integer))
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v1)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                          (coe
                                                                             addInt
                                                                             (coe (2 :: Integer))
                                                                             (coe v1)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      (1 ::
                                                                                         Integer))
                                                                                   (coe v1)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cmp-trace
d_cmp'45'trace_392 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_cmp'45'trace_392 ~v0 v1 v2 = du_cmp'45'trace_392 v1 v2
du_cmp'45'trace_392 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_cmp'45'trace_392 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2122
         (coe
            MAlonzo.Code.Once.Internal.Type.C__'42'__24
            (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
            (coe MAlonzo.Code.Once.Internal.Type.C_Int_34))
         (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block'45'info_24
            (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2138)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
               (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                                 (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                       (coe addInt (coe (1 :: Integer)) (coe v1)))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.CCC.Codegen.IRToTrace.sigop-budget
d_sigop'45'budget_398 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
d_sigop'45'budget_398 ~v0 v1 v2 = du_sigop'45'budget_398 v1 v2
du_sigop'45'budget_398 ::
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
du_sigop'45'budget_398 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (2 :: Integer)) (coe v0)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-code
d_sigop'45'code_408 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_sigop'45'code_408 ~v0 v1 v2 v3 v4 v5
  = du_sigop'45'code_408 v1 v2 v3 v4 v5
du_sigop'45'code_408 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_sigop'45'code_408 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe du_cmp'45'trace_392 (coe v5) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2122 (coe v0)
                (coe v1) (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-trace
d_sigop'45'trace_424 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'trace_424 ~v0 v1 v2 v3 v4 v5 v6
  = du_sigop'45'trace_424 v1 v2 v3 v4 v5 v6
du_sigop'45'trace_424 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'trace_424 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_sigop'45'budget_398 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_sigop'45'code_408 (coe v0) (coe v1) (coe v4) (coe v2) (coe v5))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace'
d_ir'45'to'45'trace''_438 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_438 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_ir'45'to'45'trace''_438 (coe v0) (coe v7) (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                         (coe v4) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                            (coe v4) (coe v10))))
                   (coe v9)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_ir'45'to'45'trace''_438 (coe v0) (coe v7) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                               (coe v4) (coe v10)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10))))
                         (coe v9))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_ir'45'to'45'trace''_438 (coe v0) (coe v7) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7)
                                           (coe v3) (coe v4) (coe v10)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7)
                                              (coe v3) (coe v4) (coe v10))))
                                     (coe v9)))))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v7) (coe v2)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7)
                                        (coe v3) (coe v4) (coe v10)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v7)
                                           (coe v3) (coe v4) (coe v10))))
                                  (coe v9))))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v12)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v12)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9))))
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                   (coe v3))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2096
                                            (coe v3))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              d_ir'45'to'45'trace''_438 (coe v0)
                                                              (coe v1) (coe v11)
                                                              (coe
                                                                 addInt (coe (4 :: Integer))
                                                                 (coe v3))
                                                              (coe v4) (coe v9)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_ir'45'to'45'trace''_438 (coe v0)
                                                                 (coe v1) (coe v11)
                                                                 (coe
                                                                    addInt (coe (4 :: Integer))
                                                                    (coe v3))
                                                                 (coe v4) (coe v9))))
                                                        (coe v10)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                  (coe addInt (coe (2 :: Integer)) (coe v3)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                                     (coe (2 :: Integer)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                        (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v3)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                    (coe
                                                                       addInt (coe (2 :: Integer))
                                                                       (coe v3)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                          (coe
                                                                             addInt
                                                                             (coe (3 :: Integer))
                                                                             (coe v3)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v12)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                  (coe v11)
                                                  (coe addInt (coe (4 :: Integer)) (coe v3))
                                                  (coe v4) (coe v9))))
                                         (coe v10))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                                        (coe (0 :: Integer)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                              (coe v3))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2134
                                        (coe (1 :: Integer)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                              (coe v3))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_438 (coe v0) (coe v12) (coe v2)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2) (coe v3)
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0) (coe v12) (coe v2)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2)
                                         (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                         (coe v9))))
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_ir'45'to'45'trace''_438 (coe v0) (coe v12) (coe v2)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_ir'45'to'45'trace''_438 (coe v0) (coe v11)
                                                     (coe v2) (coe v3)
                                                     (coe addInt (coe (2 :: Integer)) (coe v4))
                                                     (coe v9))))
                                            (coe v10)))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                  (coe v4))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9)))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2)
                                         (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v12) (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_438 (coe v0) (coe v11) (coe v2)
                                               (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_438 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9))))
                                         (coe v10))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0)
                                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                (coe v11) (coe (0 :: Integer))
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                   (coe v3))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                               (coe v3))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                        (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v3)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                         (coe v11) (coe (0 :: Integer))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_438 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                                                  (coe v10))
                                               (coe v11) (coe (0 :: Integer))
                                               (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_438 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                         (coe v11) (coe (0 :: Integer))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (3 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2132)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                           (coe addInt (coe (1 :: Integer)) (coe v3)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                              (coe (2 :: Integer)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                 (coe addInt (coe (2 :: Integer)) (coe v3)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                             (coe v3))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v3)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2108)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_cata'45'dispatch_274 (coe v0)
                                 (coe
                                    du_cata'45'strategy_26
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v13)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_438 (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_438 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                (coe v13) (coe v2)))
                                          (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ir'45'to'45'trace''_438 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_cata'45'dispatch_274 (coe v0)
                                       (coe
                                          du_cata'45'strategy_26
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576 (coe v13)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_438 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_438 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_438 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v2)))
                                                   (coe v2) (coe (0 :: Integer)) (coe v4)
                                                   (coe v10))))))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_cata'45'dispatch_274 (coe v0)
                                          (coe
                                             du_cata'45'strategy_26
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_576
                                                (coe v13)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_ir'45'to'45'trace''_438 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                          (coe v3)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_438 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v2)))
                                                   (coe v2) (coe (0 :: Integer)) (coe v4)
                                                   (coe v10))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_438 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                            (coe v13) (coe v2)))
                                                      (coe v2) (coe (0 :: Integer)) (coe v4)
                                                      (coe v10))))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ir'45'to'45'trace''_438 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2132)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2108)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe addInt (coe (1 :: Integer)) (coe v4))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                        (coe v3))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                 (coe v4)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (2 :: Integer)) (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_resuspend'45'layer_296 (coe v0)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                (coe v13) (coe v12))
                                             (coe (1 :: Integer))
                                             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v10)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))
                                       (coe (0 :: Integer)) (coe v13) (coe v7))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                             (coe (2 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                      (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2130
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                               (coe v0) (coe v4)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v3)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_resuspend'45'layer_296 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v12))
                                                      (coe (1 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v4))
                                                      (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                            (coe v13) (coe v12))
                                                         (coe (1 :: Integer))
                                                         (coe addInt (coe (1 :: Integer)) (coe v4))
                                                         (coe v10))))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                   (coe v4))
                                                (coe (0 :: Integer)) (coe v13) (coe v7)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               d_ir'45'to'45'trace''_438 (coe v0)
                                                               (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                  (coe v13) (coe v12))
                                                               (coe (1 :: Integer))
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v4))
                                                               (coe v10)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            d_resuspend'45'layer_296 (coe v0)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  d_ir'45'to'45'trace''_438 (coe v0)
                                                                  (coe v1)
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                     (coe v13) (coe v12))
                                                                  (coe (1 :: Integer))
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v4))
                                                                  (coe v10)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_438
                                                                     (coe v0) (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                        (coe v13) (coe v12))
                                                                     (coe (1 :: Integer))
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v4))
                                                                     (coe v10))))
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                               (coe v0) (coe v4))
                                                            (coe (0 :: Integer)) (coe v13)
                                                            (coe v7)))))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                          (coe addInt (coe (4 :: Integer)) (coe v3))
                          (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                                (coe addInt (coe (4 :: Integer)) (coe v3))
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2082)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                      (coe addInt (coe (1 :: Integer)) (coe v3)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe v4))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                            (coe
                                               MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2)
                                               (coe v11))
                                            (coe addInt (coe (4 :: Integer)) (coe v3))
                                            (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2058
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                               (coe addInt (coe (2 :: Integer)) (coe v3)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2136
                                                  (coe (2 :: Integer)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2088
                                                     (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v3)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2090)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                 (coe
                                                                    addInt (coe (2 :: Integer))
                                                                    (coe v3)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2092)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2086
                                                                       (coe
                                                                          addInt
                                                                          (coe (3 :: Integer))
                                                                          (coe v3)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2056
                                                                                (coe
                                                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                                                   (coe v0)
                                                                                   (coe v4))))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                                                                                (coe
                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2054
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                                                      (coe v0)
                                                                                      (coe
                                                                                         addInt
                                                                                         (coe
                                                                                            (1 ::
                                                                                               Integer))
                                                                                         (coe
                                                                                            v4)))))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                (coe
                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2084)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_ir'45'to'45'trace''_438 (coe v0) (coe v1)
                                      (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                                      (coe addInt (coe (4 :: Integer)) (coe v3))
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2128
                                (coe MAlonzo.Code.Once.Internal.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2128
                                (coe MAlonzo.Code.Once.Internal.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_140 v6 v7 v8
        -> coe
             du_sigop'45'trace_424 (coe v6) (coe v7) (coe v3) (coe v4) (coe v8)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v8)))
      MAlonzo.Code.Once.IR.C_Call_146 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2140
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2064
                            (coe v8)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-trace
d_proj'45'trace_736 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_proj'45'trace_736 ~v0 v1 = du_proj'45'trace_736 v1
du_proj'45'trace_736 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_proj'45'trace_736 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-bodies
d_proj'45'bodies_740 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_proj'45'bodies_740 ~v0 v1 = du_proj'45'bodies_740 v1
du_proj'45'bodies_740 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_proj'45'bodies_740 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-budget
d_proj'45'budget_744 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'budget_744 ~v0 v1 = du_proj'45'budget_744 v1
du_proj'45'budget_744 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'budget_744 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-label
d_proj'45'label_748 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'label_748 ~v0 v1 = du_proj'45'label_748 v1
du_proj'45'label_748 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'label_748 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-unit-at
d_ir'45'to'45'unit'45'at_756 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2146
d_ir'45'to'45'unit'45'at_756 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_unit_2160
      (coe
         du_proj'45'budget_744
         (coe
            d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'trace_736
         (coe
            d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'bodies_740
         (coe
            d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
-- Once.CCC.Codegen.IRToTrace.ir-to-unit
d_ir'45'to'45'unit_768 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2146
d_ir'45'to'45'unit_768 v0 v1 v2
  = coe
      d_ir'45'to'45'unit'45'at_756 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace
d_ir'45'to'45'trace_774 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_ir'45'to'45'trace_774 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2192
      (coe d_ir'45'to'45'unit_768 v0 v1 v2 v3)
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_782 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_ir'45'to'45'trace'45'at'45'frontier_782 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2192
      (coe
         d_ir'45'to'45'unit'45'at_756 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe (0 :: Integer)) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget
d_ir'45'stack'45'budget_792 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_792 v0 v1 v2 v3
  = coe
      du_proj'45'budget_744
      (coe
         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies
d_ir'45'to'45'bodies_800 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ir'45'to'45'bodies_800 v0 v1 v2 v3
  = coe
      du_proj'45'bodies_740
      (coe
         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-from
d_ir'45'to'45'trace'45'from_808 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace'45'from_808 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_822 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_822 v0 v1 v2 v3 v4
  = coe
      du_proj'45'budget_744
      (coe
         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_832 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_ir'45'to'45'trace'45'lab_832 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2192
      (coe
         d_ir'45'to'45'unit'45'at_756 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-next-label
d_ir'45'next'45'label_842 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'next'45'label_842 v0 v1 v2 v3 v4
  = coe
      du_proj'45'label_748
      (coe
         d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies-from
d_ir'45'to'45'bodies'45'from_852 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'bodies'45'from_852 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_438 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
