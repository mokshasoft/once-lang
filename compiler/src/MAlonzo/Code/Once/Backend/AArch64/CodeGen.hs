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

module MAlonzo.Code.Once.Backend.AArch64.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Backend.AArch64.Syntax
import qualified MAlonzo.Code.Once.Backend.Common.StackAnalysis
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.AArch64.CodeGen._.StackDelta
d_StackDelta_10 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_StackDelta_10
  = coe
      MAlonzo.Code.Once.Backend.Common.StackAnalysis.du_StackDelta_22
      (coe (16 :: Integer)) (coe (16 :: Integer)) (coe (16 :: Integer))
      (coe (16 :: Integer))
-- Once.Backend.AArch64.CodeGen._.StackDepth
d_StackDepth_12 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_StackDepth_12
  = coe
      MAlonzo.Code.Once.Backend.Common.StackAnalysis.d_StackDepth_42
      (coe (16 :: Integer)) (coe (16 :: Integer)) (coe (16 :: Integer))
      (coe (16 :: Integer)) (coe (16 :: Integer))
-- Once.Backend.AArch64.CodeGen.closure-setup-len
d_closure'45'setup'45'len_14 :: Integer
d_closure'45'setup'45'len_14 = coe (6 :: Integer)
-- Once.Backend.AArch64.CodeGen.thunk-setup-len
d_thunk'45'setup'45'len_16 :: Integer
d_thunk'45'setup'45'len_16 = coe (4 :: Integer)
-- Once.Backend.AArch64.CodeGen.tail-len
d_tail'45'len_18 :: Integer
d_tail'45'len_18 = coe (2 :: Integer)
-- Once.Backend.AArch64.CodeGen.thunk-entry-offset
d_thunk'45'entry'45'offset_20 :: Integer
d_thunk'45'entry'45'offset_20 = coe d_closure'45'setup'45'len_14
-- Once.Backend.AArch64.CodeGen.thunk-body-offset
d_thunk'45'body'45'offset_22 :: Integer
d_thunk'45'body'45'offset_22
  = coe
      addInt (coe d_thunk'45'setup'45'len_16)
      (coe d_closure'45'setup'45'len_14)
-- Once.Backend.AArch64.CodeGen.curry-overhead
d_curry'45'overhead_24 :: Integer
d_curry'45'overhead_24
  = coe
      addInt
      (coe
         addInt (coe d_tail'45'len_18) (coe d_thunk'45'setup'45'len_16))
      (coe d_closure'45'setup'45'len_14)
-- Once.Backend.AArch64.CodeGen.pair-overhead
d_pair'45'overhead_26 :: Integer
d_pair'45'overhead_26 = coe (11 :: Integer)
-- Once.Backend.AArch64.CodeGen.case-overhead
d_case'45'overhead_28 :: Integer
d_case'45'overhead_28 = coe (8 :: Integer)
-- Once.Backend.AArch64.CodeGen.inl-instr-len
d_inl'45'instr'45'len_30 :: Integer
d_inl'45'instr'45'len_30 = coe (4 :: Integer)
-- Once.Backend.AArch64.CodeGen.inr-instr-len
d_inr'45'instr'45'len_32 :: Integer
d_inr'45'instr'45'len_32 = coe (5 :: Integer)
-- Once.Backend.AArch64.CodeGen.apply-instr-len
d_apply'45'instr'45'len_34 :: Integer
d_apply'45'instr'45'len_34 = coe (6 :: Integer)
-- Once.Backend.AArch64.CodeGen.case-branch-offset
d_case'45'branch'45'offset_36 :: Integer
d_case'45'branch'45'offset_36 = coe (3 :: Integer)
-- Once.Backend.AArch64.CodeGen.case-jump-offset
d_case'45'jump'45'offset_38 :: Integer
d_case'45'jump'45'offset_38 = coe (3 :: Integer)
-- Once.Backend.AArch64.CodeGen.case-right-label-base
d_case'45'right'45'label'45'base_40 :: Integer
d_case'45'right'45'label'45'base_40 = coe (5 :: Integer)
-- Once.Backend.AArch64.CodeGen.case-end-label-base
d_case'45'end'45'label'45'base_42 :: Integer
d_case'45'end'45'label'45'base_42 = coe (7 :: Integer)
-- Once.Backend.AArch64.CodeGen.adr-thunk-offset
d_adr'45'thunk'45'offset_44 :: Integer
d_adr'45'thunk'45'offset_44 = coe (4 :: Integer)
-- Once.Backend.AArch64.CodeGen.curry-jump-offset
d_curry'45'jump'45'offset_46 :: Integer
d_curry'45'jump'45'offset_46 = coe (6 :: Integer)
-- Once.Backend.AArch64.CodeGen.curry-end-label-base
d_curry'45'end'45'label'45'base_48 :: Integer
d_curry'45'end'45'label'45'base_48 = coe (11 :: Integer)
-- Once.Backend.AArch64.CodeGen.compile-length
d_compile'45'length_54 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_compile'45'length_54 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe (1 :: Integer))
                (coe d_compile'45'length_54 (coe v0) (coe v4) (coe v7)))
             (coe d_compile'45'length_54 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_34 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe d_compile'45'length_54 (coe v0) (coe v9) (coe v6))
                       (coe d_compile'45'length_54 (coe v0) (coe v10) (coe v7)))
                    (coe d_pair'45'overhead_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5 -> coe d_inl'45'instr'45'len_30
      MAlonzo.Code.Once.IR.C_inr_54 v5 -> coe d_inr'45'instr'45'len_32
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe d_compile'45'length_54 (coe v8) (coe v1) (coe v6))
                       (coe d_compile'45'length_54 (coe v9) (coe v1) (coe v7)))
                    (coe d_case'45'overhead_28)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_70 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_78 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> coe
                    addInt
                    (coe
                       d_compile'45'length_54
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v8))
                       (coe v10) (coe v6))
                    (coe d_curry'45'overhead_24)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84 -> coe d_apply'45'instr'45'len_34
      MAlonzo.Code.Once.IR.C_fold_88 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_unfold_92 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_98 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_Prim_104 v5 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.AArch64.CodeGen.compile-aarch64
d_compile'45'aarch64_74 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  [MAlonzo.Code.Once.Backend.AArch64.Syntax.T_Instr_88]
d_compile'45'aarch64_74 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'aarch64_74 (coe v0) (coe v4) (coe v7))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe d_compile'45'aarch64_74 (coe v4) (coe v1) (coe v6))))
      MAlonzo.Code.Once.IR.C_fst_28
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_34
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_sndOffset_150)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                       (coe (32 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_stp_98
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_add_100
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                                   (coe (16 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe d_compile'45'aarch64_74 (coe v0) (coe v9) (coe v6))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               d_compile'45'aarch64_74 (coe v0) (coe v10) (coe v7))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.d_sndOffset_150)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldp_96
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x20_50)
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x21_52)
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                                                           (coe (0 :: Integer))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_add'45'sp_120
                                                           (coe (16 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                (coe (16 :: Integer)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str'45'zr_130
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_tagOffset_152)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_valueOffset_154)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.IR.C_inr_54 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                (coe (16 :: Integer)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                      (coe (1 :: Integer))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_tagOffset_152)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_valueOffset_154)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                       (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_cmp_104
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_tagOffset_152)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b'45'ne_110
                             (coe
                                addInt (coe d_compile'45'length_54 (coe v8) (coe v1) (coe v6))
                                (coe d_case'45'branch'45'offset_36)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.d_valueOffset_154)))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe d_compile'45'aarch64_74 (coe v8) (coe v1) (coe v6))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b_106
                                      (coe
                                         addInt
                                         (coe d_compile'45'length_54 (coe v9) (coe v1) (coe v7))
                                         (coe d_case'45'jump'45'offset_38)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                         (coe
                                            addInt
                                            (coe d_compile'45'length_54 (coe v8) (coe v1) (coe v6))
                                            (coe d_case'45'right'45'label'45'base_40)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.d_valueOffset_154)))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe d_compile'45'aarch64_74 (coe v9) (coe v1) (coe v7))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                                  (coe
                                                     addInt
                                                     (coe
                                                        addInt
                                                        (coe
                                                           d_compile'45'length_54 (coe v8) (coe v1)
                                                           (coe v6))
                                                        (coe
                                                           d_compile'45'length_54 (coe v9) (coe v1)
                                                           (coe v7)))
                                                     (coe d_case'45'end'45'label'45'base_42)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_imm_86
                   (coe (0 :: Integer))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_70
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_brk_126
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_78 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                       (coe (16 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                          (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.AArch64.Syntax.C_adr_128
                             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                             (coe d_adr'45'thunk'45'offset_44))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_str_94
                                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_sndOffset_150)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_b_106
                                      (coe
                                         addInt
                                         (coe
                                            d_compile'45'length_54
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v8))
                                            (coe v10) (coe v6))
                                         (coe d_curry'45'jump'45'offset_46)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                         (coe d_thunk'45'entry'45'offset_20))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sub'45'sp_118
                                            (coe (16 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_stp_98
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x19_48)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_sp'43'imm_78
                                                  (coe (0 :: Integer))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov'45'from'45'sp_122
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     d_compile'45'aarch64_74
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'42'__38 (coe v0)
                                                        (coe v8))
                                                     (coe v10) (coe v6))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ret_116)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.AArch64.Syntax.C_label_132
                                                           (coe
                                                              addInt
                                                              (coe
                                                                 d_compile'45'length_54
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__38
                                                                    (coe v0) (coe v8))
                                                                 (coe v10) (coe v6))
                                                              (coe
                                                                 d_curry'45'end'45'label'45'base_48)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                   (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x10_30)
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_sndOffset_150)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                      (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x19_48)
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base_74
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.Backend.AArch64.Syntax.C_ldr_92
                         (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_base'43'imm_76
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28)
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.d_sndOffset_150)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.Backend.AArch64.Syntax.C_mov_90
                            (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x0_10)
                            (coe
                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_reg_82
                               (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x10_30)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.Backend.AArch64.Syntax.C_blr_114
                               (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_x9_28))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      MAlonzo.Code.Once.IR.C_fold_88
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_unfold_92
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_arr_98
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Prim_104 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.AArch64.Syntax.C_nop_124)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
