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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Codegen.FlatLayout
import qualified MAlonzo.Code.Once.CCC.Codegen.Size
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.MuRep
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRToTrace.rec-count
d_rec'45'count_10 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
d_rec'45'count_10 ~v0 v1 = du_rec'45'count_10 v1
du_rec'45'count_10 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
du_rec'45'count_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_rec'45'count_10 (coe v1)) (coe du_rec'45'count_10 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             addInt (coe du_rec'45'count_10 (coe v1))
             (coe du_rec'45'count_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.CataStrategy
d_CataStrategy_20 a0 = ()
data T_CataStrategy_20
  = C_strat'45'const_22 | C_strat'45'box_24 |
    C_strat'45'branching_26 MAlonzo.Code.Once.Spec.Type.T_Fun_12
-- Once.CCC.Codegen.IRToTrace.box-fun
d_box'45'fun_28 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Bool
d_box'45'fun_28 ~v0 v1 = du_box'45'fun_28 v1
du_box'45'fun_28 :: MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Bool
du_box'45'fun_28 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C_K_38 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Type.C_Int_32
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                MAlonzo.Code.Once.Spec.Type.C_Float_34
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.IRToTrace.const-strategy
d_const'45'strategy_30 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Bool -> T_CataStrategy_20
d_const'45'strategy_30 ~v0 v1 = du_const'45'strategy_30 v1
du_const'45'strategy_30 :: Bool -> T_CataStrategy_20
du_const'45'strategy_30 v0
  = if coe v0 then coe C_strat'45'box_24 else coe C_strat'45'const_22
-- Once.CCC.Codegen.IRToTrace.cata-strategy
d_cata'45'strategy_32 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_CataStrategy_20
d_cata'45'strategy_32 ~v0 v1 = du_cata'45'strategy_32 v1
du_cata'45'strategy_32 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_CataStrategy_20
du_cata'45'strategy_32 v0
  = let v1 = coe du_rec'45'count_10 (coe v0) in
    coe
      (case coe v1 of
         0 -> coe du_const'45'strategy_30 (coe du_box'45'fun_28 (coe v0))
         _ -> coe C_strat'45'branching_26 (coe v0))
-- Once.CCC.Codegen.IRToTrace.cata-body
d_cata'45'body_44 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'body_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
            (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2158
               (coe
                  MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24
                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v1)))
               (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2160 (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v2))))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-call-setup
d_cata'45'call'45'setup_54 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'call'45'setup_54 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v1
         (0 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v4))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
               (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe v3))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                        (coe v2))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                 (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2228
                                    (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v5)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                       (coe (1 :: Integer)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-call-from
d_cata'45'call'45'from_66 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'call'45'from_66 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_cata'45'call'45'from_66 v1 v2 v3 v4 v5 v6 v7 v8
du_cata'45'call'45'from_66 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_cata'45'call'45'from_66 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v5))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
                  (coe
                     addInt (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v1))
                     (coe v3))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe v7))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v1 v6 v7
                     (0 :: Integer))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put'45'k_64 (coe v2)
                        (coe v3) (coe v5) (coe v7)
                        (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                           (coe v4))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2230)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                    (coe v7))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2206)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-call
d_cata'45'call_84 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'call_84 ~v0 = du_cata'45'call_84
du_cata'45'call_84 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_cata'45'call_84
  = coe
      du_cata'45'call'45'from_66
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
-- Once.CCC.Codegen.IRToTrace.cata-call-box
d_cata'45'call'45'box_86 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'call'45'box_86 ~v0 = du_cata'45'call'45'box_86
du_cata'45'call'45'box_86 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_cata'45'call'45'box_86
  = coe
      du_cata'45'call'45'from_66
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
         (coe (0 :: Integer)))
-- Once.CCC.Codegen.IRToTrace.fsize
d_fsize_88 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
d_fsize_88 ~v0 v1 = du_fsize_88 v1
du_fsize_88 :: MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
du_fsize_88 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_fsize_88 (coe v1)))
             (coe du_fsize_88 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe du_fsize_88 (coe v1)))
             (coe du_fsize_88 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.push2
d_push2_104 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_push2_104 ~v0 v1 v2 v3 = du_push2_104 v1 v2 v3
du_push2_104 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_push2_104 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
               (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                     (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                        (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                           (coe v0))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                              (coe (1 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                    (coe v0))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.pop2
d_pop2_114 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_pop2_114 ~v0 v1 = du_pop2_114 v1
du_pop2_114 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_pop2_114 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
         (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
               (coe (1 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                     (coe (0 :: Integer)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.wrap-sum
d_wrap'45'sum_126 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_wrap'45'sum_126 ~v0 v1 v2 v3 v4 v5
  = du_wrap'45'sum_126 v1 v2 v3 v4 v5
du_wrap'45'sum_126 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_wrap'45'sum_126 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
         (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
               (coe v3)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
               (coe addInt (coe (1 :: Integer)) (coe v4)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                     (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                        (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_fill_50
                           (coe addInt (coe (1 :: Integer)) (coe v2))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
                              (addInt (coe (1 :: Integer)) (coe v2))))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put'45'k_64 (coe v1)
                              (coe v2) (coe v4) (coe addInt (coe (1 :: Integer)) (coe v4))
                              (coe (1 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                 (coe addInt (coe (1 :: Integer)) (coe v4)))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Once.CCC.Codegen.IRToTrace.getL
d_getL_138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_getL_138 ~v0 v1 v2 v3 = du_getL_138 v1 v2 v3
du_getL_138 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_getL_138 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get'45'k_90
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398 (coe v0)
         (coe v1))
      (coe
         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410 (coe v0)
         (coe v2))
-- Once.CCC.Codegen.IRToTrace.getμ
d_getμ_146 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_getμ_146 ~v0 v1 = du_getμ_146 v1
du_getμ_146 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_getμ_146 v0
  = coe
      du_getL_138 (coe v0)
      (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10)
      (coe (1 :: Integer))
-- Once.CCC.Codegen.IRToTrace.lsize
d_lsize_150 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
d_lsize_150 ~v0 v1 = du_lsize_150 v1
du_lsize_150 :: MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> Integer
du_lsize_150 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v1 v2
        -> coe
             addInt
             (coe addInt (coe (2 :: Integer)) (coe du_lsize_150 (coe v1)))
             (coe du_lsize_150 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v1 v2
        -> coe
             addInt (coe du_lsize_150 (coe v1)) (coe du_lsize_150 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.visit-walk
d_visit'45'walk_170 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_visit'45'walk_170 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v7
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Spec.Type.C_Id_40
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
             (coe du_push2_104 (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_getμ_146 v8 (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         d_visit'45'walk_170 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe
                            addInt
                            (coe addInt (coe (2 :: Integer)) (coe du_lsize_150 (coe v7)))
                            (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                  (coe
                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                     (coe addInt (coe (1 :: Integer)) (coe v6)))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe du_getμ_146 v7 (1 :: Integer))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_visit'45'walk_170 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5))
                                     (coe addInt (coe (2 :: Integer)) (coe v6)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                           (coe
                                              MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                              (coe addInt (coe (1 :: Integer)) (coe v6)))))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                      (coe v5))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_getμ_146 v7 (0 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         d_visit'45'walk_170 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                               (coe v5))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe
                               du_getμ_146 v8
                               (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                  (coe v7) (coe (1 :: Integer))))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                               (coe
                                  d_visit'45'walk_170 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                                  (coe addInt (coe (4 :: Integer)) (coe v5))
                                  (coe addInt (coe du_lsize_150 (coe v7)) (coe v6)))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.rebuild-walk
d_rebuild'45'walk_230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_rebuild'45'walk_230 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_rebuild'45'walk_230 v0 v1 v4 v5 v6 v7 v8
du_rebuild'45'walk_230 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_rebuild'45'walk_230 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe du_pop2_114 (coe v1)
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe du_getμ_146 v8 (1 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_230 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe
                            addInt
                            (coe addInt (coe (2 :: Integer)) (coe du_lsize_150 (coe v7)))
                            (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            du_wrap'45'sum_126 (coe (1 :: Integer))
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398 (coe v8)
                               (coe v2))
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410 (coe v8)
                               (coe v3))
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410 (coe v4)
                               (coe v3))
                            (coe v5))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                     (coe
                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                        (coe addInt (coe (1 :: Integer)) (coe v6)))))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                        (coe
                                           MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v6))))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe du_getμ_146 v7 (1 :: Integer))
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        du_rebuild'45'walk_230 (coe v0) (coe v1) (coe v2) (coe v3)
                                        (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5))
                                        (coe addInt (coe (2 :: Integer)) (coe v6)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           du_wrap'45'sum_126 (coe (0 :: Integer))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                                              (coe v7) (coe v2))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                              (coe v7) (coe v3))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                              (coe v4) (coe v3))
                                           (coe v5))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                    (coe addInt (coe (1 :: Integer)) (coe v6)))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                      (coe v5))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_getμ_146 v8
                   (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                      (coe v7) (coe (1 :: Integer))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_230 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe du_lsize_150 (coe v7)) (coe v6)))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                               (coe addInt (coe (2 :: Integer)) (coe v5)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                  (coe v5))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe du_getμ_146 v7 (0 :: Integer))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     du_rebuild'45'walk_230 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v7) (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                           (coe addInt (coe (1 :: Integer)) (coe v5)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                 (coe (2 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                                    (coe v4) (coe v3))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                 (coe addInt (coe (3 :: Integer)) (coe v5)))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put'45'k_64
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                                              (coe v7) (coe v2))
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                              (coe v7) (coe v3))
                                           (coe addInt (coe (1 :: Integer)) (coe v5))
                                           (coe addInt (coe (3 :: Integer)) (coe v5))
                                           (coe (0 :: Integer)))
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                           (coe
                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put'45'k_64
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                                                 (coe v8) (coe v2))
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                                 (coe v8) (coe v3))
                                              (coe addInt (coe (2 :: Integer)) (coe v5))
                                              (coe addInt (coe (3 :: Integer)) (coe v5))
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                                                 (coe v7) (coe v3)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                 (coe addInt (coe (3 :: Integer)) (coe v5)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-br-I₁
d_cata'45'br'45'I'8321'_296 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'br'45'I'8321'_296 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
               (coe addInt (coe (3 :: Integer)) (coe v4)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                     (coe addInt (coe (6 :: Integer)) (coe v4)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                 (coe addInt (coe (6 :: Integer)) (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                    (coe addInt (coe (1 :: Integer)) (coe v4)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                       (coe addInt (coe (6 :: Integer)) (coe v4)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                          (coe addInt (coe (2 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                             (coe addInt (coe (6 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                (coe v4))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                   (coe addInt (coe (3 :: Integer)) (coe v4)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            du_push2_104 (coe v4) (coe addInt (coe (4 :: Integer)) (coe v4))
            (coe addInt (coe (5 :: Integer)) (coe v4)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v5))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                     (coe v4))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v5)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                              (coe (1 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                 (coe v4))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                                    (coe (0 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                          (coe addInt (coe (3 :: Integer)) (coe v4)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                             (coe addInt (coe (3 :: Integer)) (coe v4)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_push2_104 (coe addInt (coe (1 :: Integer)) (coe v4))
                  (coe addInt (coe (4 :: Integer)) (coe v4))
                  (coe addInt (coe (5 :: Integer)) (coe v4)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                        (coe addInt (coe (3 :: Integer)) (coe v4)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        d_visit'45'walk_170 (coe v0) (coe v4)
                        (coe addInt (coe (4 :: Integer)) (coe v4))
                        (coe addInt (coe (5 :: Integer)) (coe v4)) (coe v3)
                        (coe addInt (coe (7 :: Integer)) (coe v4))
                        (coe addInt (coe (4 :: Integer)) (coe v5)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v5))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v5)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v5)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                    (coe addInt (coe (1 :: Integer)) (coe v4)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v5)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                                             (coe (1 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                (coe addInt (coe (1 :: Integer)) (coe v4)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 du_rebuild'45'walk_230 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v1) (coe v2)
                                 (coe v3) (coe addInt (coe (7 :: Integer)) (coe v4))
                                 (coe
                                    addInt
                                    (coe addInt (coe (4 :: Integer)) (coe du_lsize_150 (coe v3)))
                                    (coe v5)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-br-I₂
d_cata'45'br'45'I'8322'_308 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cata'45'br'45'I'8322'_308 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         du_push2_104 (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                     (coe addInt (coe (2 :: Integer)) (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                     (coe
                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                        (coe addInt (coe (3 :: Integer)) (coe v2)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
               (coe addInt (coe (2 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                     (coe (0 :: Integer)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-branching
d_cata'45'trace'45'branching_314 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_314 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            addInt (coe (15 :: Integer))
            (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
         (coe v5))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt
            (coe
               addInt
               (coe addInt (coe (6 :: Integer)) (coe du_lsize_150 (coe v3)))
               (coe du_lsize_150 (coe v3)))
            (coe v6))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_54 (coe v0) (coe v1)
               (coe
                  addInt
                  (coe
                     addInt (coe (11 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                  (coe v5))
               (coe
                  addInt
                  (coe
                     addInt (coe (12 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                  (coe v5))
               (coe
                  addInt
                  (coe
                     addInt (coe (13 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                  (coe v5))
               (coe
                  addInt
                  (coe
                     addInt
                     (coe addInt (coe (4 :: Integer)) (coe du_lsize_150 (coe v3)))
                     (coe du_lsize_150 (coe v3)))
                  (coe v6)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  d_cata'45'br'45'I'8321'_296 (coe v0)
                  (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14 (coe v2))
                  (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v2)) (coe v3)
                  (coe v5) (coe v6))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     du_cata'45'call_84 v1
                     (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                        (coe v3)
                        (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14 (coe v2)))
                     (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                        (coe v3)
                        (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v2)))
                     (addInt
                        (coe
                           addInt (coe (11 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                        (coe v5))
                     (addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                        (coe v5))
                     (addInt
                        (coe
                           addInt (coe (13 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                        (coe v5))
                     (addInt
                        (coe
                           addInt (coe (14 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_88 (coe v3))))
                        (coe v5)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe d_cata'45'br'45'I'8322'_308 (coe v0) (coe v5) (coe v6))
                     (coe
                        d_cata'45'body_44 (coe v0)
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (4 :: Integer)) (coe du_lsize_150 (coe v3)))
                              (coe du_lsize_150 (coe v3)))
                           (coe v6))
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (5 :: Integer)) (coe du_lsize_150 (coe v3)))
                              (coe du_lsize_150 (coe v3)))
                           (coe v6))
                        (coe v4) (coe v7)))))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-const
d_cata'45'trace'45'const_330 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_330 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (4 :: Integer)) (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (2 :: Integer)) (coe v5))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_54 (coe v0) (coe v1) (coe v4)
               (coe addInt (coe (1 :: Integer)) (coe v4))
               (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_cata'45'call_84 v1
                  (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                     (coe v2) (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10))
                  (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                     (coe v2) (coe (1 :: Integer)))
                  v4 (addInt (coe (1 :: Integer)) (coe v4))
                  (addInt (coe (2 :: Integer)) (coe v4))
                  (addInt (coe (3 :: Integer)) (coe v4)))
               (coe
                  d_cata'45'body_44 (coe v0) (coe v5)
                  (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3) (coe v6)))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-box
d_cata'45'trace'45'box_344 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'box_344 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (4 :: Integer)) (coe v4))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (2 :: Integer)) (coe v5))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_54 (coe v0) (coe v1) (coe v4)
               (coe addInt (coe (1 :: Integer)) (coe v4))
               (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v5))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_cata'45'call'45'box_86 v1
                  (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lkind_398
                     (coe v2) (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10))
                  (MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_lsz_410
                     (coe v2) (coe (1 :: Integer)))
                  v4 (addInt (coe (1 :: Integer)) (coe v4))
                  (addInt (coe (2 :: Integer)) (coe v4))
                  (addInt (coe (3 :: Integer)) (coe v4)))
               (coe
                  d_cata'45'body_44 (coe v0) (coe v5)
                  (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v3) (coe v6)))))
-- Once.CCC.Codegen.IRToTrace.cata-dispatch
d_cata'45'dispatch_358 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_358 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      C_strat'45'const_22
        -> coe
             d_cata'45'trace'45'const_330 (coe v0) (coe v1) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8)
      C_strat'45'box_24
        -> coe
             d_cata'45'trace'45'box_344 (coe v0) (coe v1) (coe v3) (coe v5)
             (coe v6) (coe v7) (coe v8)
      C_strat'45'branching_26 v9
        -> coe
             d_cata'45'trace'45'branching_314 (coe v0) (coe v1) (coe v2)
             (coe v9) (coe v5) (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.resuspend-layer
d_resuspend'45'layer_406 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_132 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_136 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (4 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                            (coe v7))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v2
                         (0 :: Integer))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                               (coe addInt (coe (1 :: Integer)) (coe v4)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                  (coe
                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                        (coe
                                           MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v3)))))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                     (coe addInt (coe (2 :: Integer)) (coe v4)))
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe
                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v2
                               (addInt (coe (1 :: Integer)) (coe v4))
                               (addInt (coe (2 :: Integer)) (coe v4)) (0 :: Integer))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                               (coe
                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v3 v4
                                  (addInt (coe (2 :: Integer)) (coe v4))
                                  (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v2)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                     (coe (2 :: Integer)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                        (coe addInt (coe (3 :: Integer)) (coe v4)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                              (coe addInt (coe (2 :: Integer)) (coe v4)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                                 (coe (0 :: Integer)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2228
                                                    (coe v6))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                                       (coe (1 :: Integer)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                          (coe
                                                             addInt (coe (3 :: Integer)) (coe v4)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_144 v12 v13
        -> case coe v8 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v14 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe addInt (coe (3 :: Integer)) (coe v4))
                                (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v6) (coe v7)
                                (coe v14) (coe v12)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe addInt (coe (3 :: Integer)) (coe v4))
                                   (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v6) (coe v7)
                                   (coe v14) (coe v12))))
                          (coe v6) (coe v7) (coe v15) (coe v13)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                      (coe addInt (coe (3 :: Integer)) (coe v4))
                                      (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v6) (coe v7)
                                      (coe v14) (coe v12)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe addInt (coe (3 :: Integer)) (coe v4))
                                         (coe addInt (coe (2 :: Integer)) (coe v5)) (coe v6)
                                         (coe v7) (coe v14) (coe v12))))
                                (coe v6) (coe v7) (coe v15) (coe v13))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                (coe v4))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                   (coe v4))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v5))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                      (coe v4))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                      (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                         (coe v15) (coe v3))
                                      (1 :: Integer))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2)
                                               (coe v3)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     d_resuspend'45'layer_406 (coe v0) (coe v1)
                                                     (coe v2) (coe v3)
                                                     (coe addInt (coe (3 :: Integer)) (coe v4))
                                                     (coe addInt (coe (2 :: Integer)) (coe v5))
                                                     (coe v6) (coe v7) (coe v14) (coe v12)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        d_resuspend'45'layer_406 (coe v0) (coe v1)
                                                        (coe v2) (coe v3)
                                                        (coe addInt (coe (3 :: Integer)) (coe v4))
                                                        (coe addInt (coe (2 :: Integer)) (coe v5))
                                                        (coe v6) (coe v7) (coe v14) (coe v12))))
                                               (coe v6) (coe v7) (coe v15) (coe v13))))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                               (coe addInt (coe (2 :: Integer)) (coe v4)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                     (coe (2 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.C__'43'__22
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                              (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                 (coe v1)))
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                              (coe v15)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                 (coe v1)))))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                     (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                                                           (coe (1 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                                              (coe (0 :: Integer)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_fill_50
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                        (coe v15)
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                           (coe v1)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                  (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.C__'43'__22
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                              (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v15)
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                              (coe v1)))))
                                                  (addInt
                                                     (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v15)
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                              (coe v1)))))))
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                  (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                     (coe v15)
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                        (coe v1)))
                                                  (addInt (coe (2 :: Integer)) (coe v4))
                                                  (addInt (coe (1 :: Integer)) (coe v4))
                                                  (1 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                     (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe v5))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                            (coe v4))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                            (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                               (coe v14) (coe v3))
                                            (1 :: Integer))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_resuspend'45'layer_406 (coe v0) (coe v1)
                                                     (coe v2) (coe v3)
                                                     (coe addInt (coe (3 :: Integer)) (coe v4))
                                                     (coe addInt (coe (2 :: Integer)) (coe v5))
                                                     (coe v6) (coe v7) (coe v14) (coe v12))))
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                     (coe addInt (coe (2 :: Integer)) (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe (2 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.C__'43'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                    (coe v14)
                                                                    (coe
                                                                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                    (coe v15)
                                                                    (coe
                                                                       MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                       (coe v1)))))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v4)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                                                    (coe (0 :: Integer)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_fill_50
                                                     (coe
                                                        addInt (coe (1 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                              (coe v14)
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                 (coe v1)))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                        (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C__'43'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                 (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                 (coe v15)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                    (coe v1)))))
                                                        (addInt
                                                           (coe (1 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                 (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                    (coe v1)))))))
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                        (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                              (coe v1)))
                                                        (addInt (coe (2 :: Integer)) (coe v4))
                                                        (addInt (coe (1 :: Integer)) (coe v4))
                                                        (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v4)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v5)))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_150 v12 v13
        -> case coe v8 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v14 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v6)
                                (coe v7) (coe v14) (coe v12)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v6)
                                   (coe v7) (coe v14) (coe v12))))
                          (coe v6) (coe v7) (coe v15) (coe v13)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2) (coe v3)
                                      (coe addInt (coe (4 :: Integer)) (coe v4)) (coe v5) (coe v6)
                                      (coe v7) (coe v14) (coe v12)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe addInt (coe (4 :: Integer)) (coe v4))
                                         (coe v5) (coe v6) (coe v7) (coe v14) (coe v12))))
                                (coe v6) (coe v7) (coe v15) (coe v13))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                (coe v4))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                   (coe v4))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v14) (coe v3))
                                (0 :: Integer))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_406 (coe v0) (coe v1) (coe v2)
                                         (coe v3) (coe addInt (coe (4 :: Integer)) (coe v4))
                                         (coe v5) (coe v6) (coe v7) (coe v14) (coe v12))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                         (coe addInt (coe (2 :: Integer)) (coe v4)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                                            (coe v4))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                         (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                            (coe v15) (coe v3))
                                         (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                            (coe
                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                               (coe v14) (coe v3))))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_resuspend'45'layer_406 (coe v0) (coe v1)
                                                  (coe v2) (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        d_resuspend'45'layer_406 (coe v0) (coe v1)
                                                        (coe v2) (coe v3)
                                                        (coe addInt (coe (4 :: Integer)) (coe v4))
                                                        (coe v5) (coe v6) (coe v7) (coe v14)
                                                        (coe v12)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_resuspend'45'layer_406 (coe v0)
                                                           (coe v1) (coe v2) (coe v3)
                                                           (coe
                                                              addInt (coe (4 :: Integer)) (coe v4))
                                                           (coe v5) (coe v6) (coe v7) (coe v14)
                                                           (coe v12))))
                                                  (coe v6) (coe v7) (coe v15) (coe v13))))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                  (coe addInt (coe (3 :: Integer)) (coe v4)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe (2 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C__'42'__20
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                 (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                                 (coe v15)
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                                    (coe v1)))))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                        (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                  (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                     (coe v14)
                                                     (coe
                                                        MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                        (coe v1)))
                                                  (addInt (coe (2 :: Integer)) (coe v4))
                                                  (addInt (coe (1 :: Integer)) (coe v4))
                                                  (0 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                     (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                        (coe v15)
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                           (coe v1)))
                                                     (addInt (coe (3 :: Integer)) (coe v4))
                                                     (addInt (coe (1 :: Integer)) (coe v4))
                                                     (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v14)
                                                           (coe
                                                              MAlonzo.Code.Once.IRTy.C_ν'45'type_28
                                                              (coe v1)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                        (coe addInt (coe (1 :: Integer)) (coe v4)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cmp-trace
d_cmp'45'trace_540 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_cmp'45'trace_540 ~v0 v1 v2 = du_cmp'45'trace_540 v1 v2
du_cmp'45'trace_540 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_cmp'45'trace_540 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2220
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'42'__22
            (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
            (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block'45'info_24
            (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2236)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
               (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                              (coe (0 :: Integer)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Once.CCC.Codegen.IRToTrace.sigop-budget
d_sigop'45'budget_546 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
d_sigop'45'budget_546 ~v0 v1 v2 = du_sigop'45'budget_546 v1 v2
du_sigop'45'budget_546 ::
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
du_sigop'45'budget_546 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (2 :: Integer)) (coe v0)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-code
d_sigop'45'code_556 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_sigop'45'code_556 ~v0 v1 v2 v3 v4 v5
  = du_sigop'45'code_556 v1 v2 v3 v4 v5
du_sigop'45'code_556 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_sigop'45'code_556 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe du_cmp'45'trace_540 (coe v5) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2220 (coe v0)
                (coe v1) (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-trace
d_sigop'45'trace_572 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'trace_572 ~v0 v1 v2 v3 v4 v5 v6
  = du_sigop'45'trace_572 v1 v2 v3 v4 v5 v6
du_sigop'45'trace_572 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'trace_572 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_sigop'45'budget_546 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_sigop'45'code_556 (coe v0) (coe v1) (coe v4) (coe v2) (coe v5))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.IRToTrace.in-box-trace
d_in'45'box'45'trace_582 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_in'45'box'45'trace_582 ~v0 v1 = du_in'45'box'45'trace_582 v1
du_in'45'box'45'trace_582 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_in'45'box'45'trace_582 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
               (coe (2 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                     (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                        (coe (0 :: Integer)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.CCC.Codegen.IRToTrace.node-copy-trace
d_node'45'copy'45'trace_586 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_node'45'copy'45'trace_586 ~v0 v1 v2
  = du_node'45'copy'45'trace_586 v1 v2
du_node'45'copy'45'trace_586 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_node'45'copy'45'trace_586 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
                  (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe addInt (coe (1 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v0 v1
                     (addInt (coe (1 :: Integer)) (coe v1)) (0 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                        (coe addInt (coe (1 :: Integer)) (coe v1)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.CCC.Codegen.IRToTrace.in-ptr-trace
d_in'45'ptr'45'trace_592 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_in'45'ptr'45'trace_592 ~v0 v1 v2 v3
  = du_in'45'ptr'45'trace_592 v1 v2 v3
du_in'45'ptr'45'trace_592 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_in'45'ptr'45'trace_592 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12
        -> coe du_node'45'copy'45'trace_586 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.in-ptr-next
d_in'45'ptr'45'next_602 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
d_in'45'ptr'45'next_602 ~v0 v1 v2 = du_in'45'ptr'45'next_602 v1 v2
du_in'45'ptr'45'next_602 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
du_in'45'ptr'45'next_602 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10 -> coe v1
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12
        -> coe addInt (coe (2 :: Integer)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.in-trace
d_in'45'trace_608 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_in'45'trace_608 ~v0 v1 v2 v3 v4 = du_in'45'trace_608 v1 v2 v3 v4
du_in'45'trace_608 ::
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_in'45'trace_608 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'box_10
        -> coe du_in'45'box'45'trace_582 (coe v3)
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'unit_12
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                (coe (2 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'ptr_14
        -> coe du_in'45'ptr'45'trace_592 (coe v1) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.in-next
d_in'45'next_628 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
d_in'45'next_628 ~v0 v1 v2 v3 = du_in'45'next_628 v1 v2 v3
du_in'45'next_628 ::
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
du_in'45'next_628 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'box_10
        -> coe addInt (coe (1 :: Integer)) (coe v2)
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'unit_12 -> coe v2
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'ptr_14
        -> coe du_in'45'ptr'45'next_602 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.with-copy
d_with'45'copy_642 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_with'45'copy_642 ~v0 v1 v2 v3 v4
  = du_with'45'copy_642 v1 v2 v3 v4
du_with'45'copy_642 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  (Integer ->
   [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_with'45'copy_642 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10 -> coe v3 v2
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe du_node'45'copy'45'trace_586 (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                (coe v3 (addInt (coe (2 :: Integer)) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.copy-next
d_copy'45'next_656 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
d_copy'45'next_656 ~v0 v1 v2 = du_copy'45'next_656 v1 v2
du_copy'45'next_656 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  Integer -> Integer
du_copy'45'next_656 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10 -> coe v1
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12
        -> coe addInt (coe (2 :: Integer)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.two-cell
d_two'45'cell_662 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_two'45'cell_662 ~v0 v1 v2 = du_two'45'cell_662 v1 v2
du_two'45'cell_662 ::
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_two'45'cell_662 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
               (coe (2 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe addInt (coe (1 :: Integer)) (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                        (coe v0))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2228
                              (coe v1))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                 (coe (1 :: Integer)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                    (coe addInt (coe (1 :: Integer)) (coe v0)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.out-trace
d_out'45'trace_668 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_out'45'trace_668 ~v0 v1 = du_out'45'trace_668 v1
du_out'45'trace_668 ::
  MAlonzo.Code.Once.CCC.Machine.MuRep.T_MuRep_8 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_out'45'trace_668 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'box_10
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'unit_12
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.MuRep.C_mu'45'ptr_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.inj-trace
d_inj'45'trace_670 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_inj'45'trace_670 ~v0 v1 v2 v3 v4
  = du_inj'45'trace_670 v1 v2 v3 v4
du_inj'45'trace_670 ::
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_inj'45'trace_670 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
                  (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v2))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe addInt (coe (1 :: Integer)) (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2232
                        (coe v0))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_fill_50
                              (coe
                                 addInt (coe (1 :: Integer))
                                 (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v1)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                 (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v2))
                                 (addInt
                                    (coe (1 :: Integer))
                                    (coe MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v1)))))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v1 v3
                                 (addInt (coe (1 :: Integer)) (coe v3)) (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.env-prologue
d_env'45'prologue_680 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_env'45'prologue_680 ~v0 v1 v2 = du_env'45'prologue_680 v1 v2
du_env'45'prologue_680 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_env'45'prologue_680 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
               (coe (0 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                  (coe (1 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v1
                        (1 :: Integer))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe (2 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                 (coe (3 :: Integer)))
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe
                                    MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v0
                                    (1 :: Integer) (3 :: Integer) (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86 v1
                                       (2 :: Integer) (3 :: Integer)
                                       (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                          (coe (3 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
-- Once.CCC.Codegen.IRToTrace.env-entry
d_env'45'entry_686 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_env'45'entry_686 ~v0 v1 v2 v3 = du_env'45'entry_686 v1 v2 v3
du_env'45'entry_686 ::
  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.T_Kind_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_env'45'entry_686 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_word_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (4 :: Integer))
             (coe du_env'45'prologue_680 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-trace'
d_ir'45'to'45'trace''_700 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_700 v0 v1 v2 v3 v4 v5
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
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_ir'45'to'45'trace''_700 (coe v0) (coe v7) (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
                         (coe v4) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
                            (coe v4) (coe v10))))
                   (coe v9)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_ir'45'to'45'trace''_700 (coe v0) (coe v7) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
                               (coe v4) (coe v10)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
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
                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_ir'45'to'45'trace''_700 (coe v0) (coe v7) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7)
                                           (coe v3) (coe v4) (coe v10)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7)
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
                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v7) (coe v2)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7)
                                        (coe v3) (coe v4) (coe v10)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v7)
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
                          d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v12)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v12)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9))))
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
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
                                               d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2194
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
                                                        d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              d_ir'45'to'45'trace''_700 (coe v0)
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
                                                                 d_ir'45'to'45'trace''_700 (coe v0)
                                                                 (coe v1) (coe v11)
                                                                 (coe
                                                                    addInt (coe (4 :: Integer))
                                                                    (coe v3))
                                                                 (coe v4) (coe v9))))
                                                        (coe v10)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                  (coe addInt (coe (2 :: Integer)) (coe v3)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe (2 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                           (coe v2))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                        (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                           v11
                                                           (addInt (coe (1 :: Integer)) (coe v3))
                                                           (addInt (coe (3 :: Integer)) (coe v3))
                                                           (0 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                              v12
                                                              (addInt (coe (2 :: Integer)) (coe v3))
                                                              (addInt (coe (3 :: Integer)) (coe v3))
                                                              (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                                 (coe v11)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                                 (coe
                                                                    addInt (coe (3 :: Integer))
                                                                    (coe v3)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v12)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
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
                      MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v2
                      (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_snd_48
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v2
                             (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8 (coe v8)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_54
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_inj'45'trace_670 (coe (0 :: Integer)) (coe v1)
                             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v9))
                             (coe v3))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_60
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_inj'45'trace_670 (coe (1 :: Integer)) (coe v1)
                             (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v8) (coe v1))
                             (coe v3))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_700 (coe v0) (coe v12) (coe v2)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2) (coe v3)
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_700 (coe v0) (coe v12) (coe v2)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2)
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
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v12
                                   (1 :: Integer))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v12)
                                                  (coe v2)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        d_ir'45'to'45'trace''_700 (coe v0) (coe v11)
                                                        (coe v2) (coe v3)
                                                        (coe addInt (coe (2 :: Integer)) (coe v4))
                                                        (coe v9)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_ir'45'to'45'trace''_700 (coe v0)
                                                           (coe v11) (coe v2) (coe v3)
                                                           (coe
                                                              addInt (coe (2 :: Integer)) (coe v4))
                                                           (coe v9))))
                                                  (coe v10)))))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                     (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                        (coe v4))))
                                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                               v11 (1 :: Integer))
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              d_ir'45'to'45'trace''_700 (coe v0)
                                                              (coe v11) (coe v2) (coe v3)
                                                              (coe
                                                                 addInt (coe (2 :: Integer))
                                                                 (coe v4))
                                                              (coe v9)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                              (coe v0)
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v4)))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2)
                                         (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v12) (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_700 (coe v0) (coe v11) (coe v2)
                                               (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_700 (coe v0) (coe v11)
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
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_curry_86 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v11 v12 v13
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe
                          du_copy'45'next_656
                          (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14 (coe v1))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_700 (coe v0)
                                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                (coe v13)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_env'45'entry_686
                                      (coe
                                         MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                         (coe v1))
                                      (coe v1) (coe v11)))
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_with'45'copy_642
                             (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14 (coe v1))
                             (coe v1) (coe v3)
                             (coe
                                (\ v14 ->
                                   coe
                                     du_two'45'cell_662 (coe v14)
                                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4)))))
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
                                         d_ir'45'to'45'trace''_700 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               du_env'45'entry_686
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                                  (coe v1))
                                               (coe v1) (coe v11)))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v10)))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_env'45'entry_686
                                            (coe
                                               MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                               (coe v1))
                                            (coe v1) (coe v11)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_700 (coe v0)
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                                                     (coe v11))
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        du_env'45'entry_686
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                                           (coe v1))
                                                        (coe v1) (coe v11)))
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v10))))))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_700 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                         (coe v13)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               du_env'45'entry_686
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                                  (coe v1))
                                               (coe v1) (coe v11)))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v10))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (3 :: Integer)) (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe
                                       MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v11
                                       (1 :: Integer))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                                             (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2230)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                                                      (coe (0 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                            (coe
                                                               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                               (coe (2 :: Integer))
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                                     (coe v11)))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                               (coe
                                                                  addInt (coe (2 :: Integer))
                                                                  (coe v3)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v3)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2246
                                                                        (coe (0 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                                           v11 v3
                                                                           (addInt
                                                                              (coe (2 :: Integer))
                                                                              (coe v3))
                                                                           (1 :: Integer))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (2 :: Integer))
                                                                                 (coe v3)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2206)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_In_98 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_in'45'next_628
                       (coe MAlonzo.Code.Once.CCC.Machine.MuRep.d_mu'45'rep_16 (coe v8))
                       (coe
                          MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2)))
                       (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_in'45'trace_608
                             (coe MAlonzo.Code.Once.CCC.Machine.MuRep.d_mu'45'rep_16 (coe v8))
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2)))
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2))
                             (coe v3))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_out'45'trace_668
                             (coe MAlonzo.Code.Once.CCC.Machine.MuRep.d_mu'45'rep_16 (coe v8)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_110 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_cata'45'dispatch_358 (coe v0) (coe v11) (coe v2)
                                 (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606 (coe v13))
                                 (coe
                                    du_cata'45'strategy_32
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606 (coe v13)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_700 (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_700 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                (coe v13) (coe v2)))
                                          (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ir'45'to'45'trace''_700 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_cata'45'dispatch_358 (coe v0) (coe v11) (coe v2)
                                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606 (coe v13))
                                       (coe
                                          du_cata'45'strategy_32
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606 (coe v13)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_700 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_700 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_700 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                          d_cata'45'dispatch_358 (coe v0) (coe v11) (coe v2)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606 (coe v13))
                                          (coe
                                             du_cata'45'strategy_32
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_606
                                                (coe v13)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_ir'45'to'45'trace''_700 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                          (coe v3)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_700 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                                      d_ir'45'to'45'trace''_700 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                             d_ir'45'to'45'trace''_700 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2230)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2244
                            (coe (0 :: Integer)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2206)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe
                          du_copy'45'next_656
                          (coe
                             MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2)))
                          (coe v3)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe addInt (coe (1 :: Integer)) (coe v4))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_with'45'copy_642
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_kind_14
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2)))
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v8) (coe v2))
                             (coe v3)
                             (coe
                                (\ v9 ->
                                   coe
                                     du_two'45'cell_662 (coe v9)
                                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4)))))
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
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_126 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (4 :: Integer)) (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_resuspend'45'layer_406 (coe v0) (coe v13) (coe v11)
                                       (coe v12)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                (coe v13) (coe v12))
                                             (coe (1 :: Integer))
                                             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v10)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0) (coe v4))
                                       (coe (0 :: Integer)) (coe v13) (coe v7))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    du_with'45'copy_642
                                    (coe MAlonzo.Code.Once.CCC.Codegen.FlatLayout.C_flat_12)
                                    (coe v1) (coe v3)
                                    (coe
                                       (\ v14 ->
                                          coe
                                            du_two'45'cell_662 (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe v4)))))
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
                                                d_resuspend'45'layer_406 (coe v0) (coe v13)
                                                (coe v11) (coe v12)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                         (coe v13) (coe v12))
                                                      (coe (1 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v4))
                                                      (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2176)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
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
                                                               d_ir'45'to'45'trace''_700 (coe v0)
                                                               (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                                            d_resuspend'45'layer_406 (coe v0)
                                                            (coe v13) (coe v11) (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  d_ir'45'to'45'trace''_700 (coe v0)
                                                                  (coe v1)
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                                                     d_ir'45'to'45'trace''_700
                                                                     (coe v0) (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
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
                                                d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
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
                                d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                                (coe addInt (coe (4 :: Integer)) (coe v3))
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v10
                                (0 :: Integer))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                      (coe addInt (coe (1 :: Integer)) (coe v3)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                               (coe v4))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2)
                                                  (coe v11))
                                               (coe addInt (coe (4 :: Integer)) (coe v3))
                                               (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2156
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Label.d_ℓ_300 (coe v0)
                                                     (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124 v11
                                            (1 :: Integer))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                  (coe addInt (coe (2 :: Integer)) (coe v3)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2234
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe (2 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                           (coe v1))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2186
                                                        (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                  v10 (addInt (coe (1 :: Integer)) (coe v3))
                                                  (addInt (coe (3 :: Integer)) (coe v3))
                                                  (0 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_put_86
                                                     v11 (addInt (coe (2 :: Integer)) (coe v3))
                                                     (addInt (coe (3 :: Integer)) (coe v3))
                                                     (MAlonzo.Code.Once.CCC.Codegen.Size.d_size_8
                                                        (coe v10)))
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2184
                                                           (coe
                                                              addInt (coe (3 :: Integer)) (coe v3)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2178)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2154
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                                       (coe v0) (coe v4))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2152
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_300
                                                                          (coe v0)
                                                                          (coe
                                                                             addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe v4)))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Codegen.FlatLayout.d_get_124
                                                        v2 (1 :: Integer)))))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_ir'45'to'45'trace''_700 (coe v0) (coe v1)
                                      (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v11))
                                      (coe addInt (coe (4 :: Integer)) (coe v3))
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_554
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2226
                                (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'int_26) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_556
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2226
                                (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'float_28) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_144 v6 v7 v8
        -> coe
             du_sigop'45'trace_572 (coe v6) (coe v7) (coe v3) (coe v4) (coe v8)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_118 (coe v8)))
      MAlonzo.Code.Once.IR.C_Call_150 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2238
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2162
                            (coe v8)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-trace
d_proj'45'trace_1042 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_proj'45'trace_1042 ~v0 v1 = du_proj'45'trace_1042 v1
du_proj'45'trace_1042 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
du_proj'45'trace_1042 v0
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
d_proj'45'bodies_1046 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_proj'45'bodies_1046 ~v0 v1 = du_proj'45'bodies_1046 v1
du_proj'45'bodies_1046 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_proj'45'bodies_1046 v0
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
d_proj'45'budget_1050 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'budget_1050 ~v0 v1 = du_proj'45'budget_1050 v1
du_proj'45'budget_1050 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'budget_1050 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-label
d_proj'45'label_1054 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'label_1054 ~v0 v1 = du_proj'45'label_1054 v1
du_proj'45'label_1054 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'label_1054 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-unit-at
d_ir'45'to'45'unit'45'at_1062 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2254
d_ir'45'to'45'unit'45'at_1062 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_unit_2268
      (coe
         du_proj'45'budget_1050
         (coe
            d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'trace_1042
         (coe
            d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'bodies_1046
         (coe
            d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
-- Once.CCC.Codegen.IRToTrace.ir-to-unit
d_ir'45'to'45'unit_1074 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2254
d_ir'45'to'45'unit_1074 v0 v1 v2
  = coe
      d_ir'45'to'45'unit'45'at_1062 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace
d_ir'45'to'45'trace_1080 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_ir'45'to'45'trace_1080 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2300
      (coe d_ir'45'to'45'unit_1074 v0 v1 v2 v3)
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_1088 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_ir'45'to'45'trace'45'at'45'frontier_1088 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2300
      (coe
         d_ir'45'to'45'unit'45'at_1062 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe (0 :: Integer)) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget
d_ir'45'stack'45'budget_1098 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_1098 v0 v1 v2 v3
  = coe
      du_proj'45'budget_1050
      (coe
         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies
d_ir'45'to'45'bodies_1106 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ir'45'to'45'bodies_1106 v0 v1 v2 v3
  = coe
      du_proj'45'bodies_1046
      (coe
         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-from
d_ir'45'to'45'trace'45'from_1114 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace'45'from_1114 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_1128 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_1128 v0 v1 v2 v3 v4
  = coe
      du_proj'45'budget_1050
      (coe
         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_1138 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2174]
d_ir'45'to'45'trace'45'lab_1138 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2300
      (coe
         d_ir'45'to'45'unit'45'at_1062 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-next-label
d_ir'45'next'45'label_1148 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'next'45'label_1148 v0 v1 v2 v3 v4
  = coe
      du_proj'45'label_1054
      (coe
         d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies-from
d_ir'45'to'45'bodies'45'from_1158 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'bodies'45'from_1158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_700 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
