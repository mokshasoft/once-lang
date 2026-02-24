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

module MAlonzo.Code.Once.Backend.X86.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Backend.X86.Syntax
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.X86.CodeGen.simple-instr-count
d_simple'45'instr'45'count_8 :: Integer
d_simple'45'instr'45'count_8 = coe (1 :: Integer)
-- Once.Backend.X86.CodeGen.inl-instrs
d_inl'45'instrs_10 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_inl'45'instrs_10
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
               (coe (0 :: Integer))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.Backend.X86.CodeGen.inr-instrs
d_inr'45'instrs_12 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_inr'45'instrs_12
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
               (coe (1 :: Integer))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Once.Backend.X86.CodeGen.injection-instr-count
d_injection'45'instr'45'count_14 :: Integer
d_injection'45'instr'45'count_14
  = coe MAlonzo.Code.Data.List.Base.du_length_268 d_inl'45'instrs_10
-- Once.Backend.X86.CodeGen.injection-consumed-slots
d_injection'45'consumed'45'slots_16 :: Integer
d_injection'45'consumed'45'slots_16
  = coe
      MAlonzo.Code.Once.Backend.X86.Syntax.d_instrs'45'consumed'45'slots_134
      d_inl'45'instrs_10
-- Once.Backend.X86.CodeGen.apply-instrs
d_apply'45'instrs_18 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_apply'45'instrs_18
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsi_18))
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r12_34))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsi_18)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_call_78
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.Backend.X86.CodeGen.apply-instr-count
d_apply'45'instr'45'count_20 :: Integer
d_apply'45'instr'45'count_20
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268 d_apply'45'instrs_18
-- Once.Backend.X86.CodeGen.pair-setup
d_pair'45'setup_22 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_pair'45'setup_22
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r14_38)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
                           (coe (2 :: Integer)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r14_38))
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.Backend.X86.CodeGen.pair-middle
d_pair'45'middle_24 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_pair'45'middle_24
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r14_38)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Backend.X86.CodeGen.pair-cleanup
d_pair'45'cleanup_26 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_pair'45'cleanup_26
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r14_38))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.Backend.X86.CodeGen.pair-overhead
d_pair'45'overhead_28 :: Integer
d_pair'45'overhead_28
  = coe
      addInt
      (coe
         addInt
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'cleanup_26)
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'middle_24))
      (coe MAlonzo.Code.Data.List.Base.du_length_268 d_pair'45'setup_22)
-- Once.Backend.X86.CodeGen.case-setup-count
d_case'45'setup'45'count_30 :: Integer
d_case'45'setup'45'count_30 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.case-prefix-count
d_case'45'prefix'45'count_32 :: Integer
d_case'45'prefix'45'count_32 = coe (4 :: Integer)
-- Once.Backend.X86.CodeGen.case-middle-count
d_case'45'middle'45'count_34 :: Integer
d_case'45'middle'45'count_34 = coe (3 :: Integer)
-- Once.Backend.X86.CodeGen.case-cleanup-count
d_case'45'cleanup'45'count_36 :: Integer
d_case'45'cleanup'45'count_36 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.case-overhead
d_case'45'overhead_38 :: Integer
d_case'45'overhead_38
  = coe
      addInt
      (coe
         addInt
         (coe
            addInt (coe d_case'45'cleanup'45'count_36)
            (coe d_case'45'middle'45'count_34))
         (coe d_case'45'prefix'45'count_32))
      (coe d_case'45'setup'45'count_30)
-- Once.Backend.X86.CodeGen.case-setup-prefix-count
d_case'45'setup'45'prefix'45'count_40 :: Integer
d_case'45'setup'45'prefix'45'count_40
  = coe
      addInt (coe d_case'45'prefix'45'count_32)
      (coe d_case'45'setup'45'count_30)
-- Once.Backend.X86.CodeGen.case-jne-base
d_case'45'jne'45'base_42 :: Integer
d_case'45'jne'45'base_42 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.case-jmp-base
d_case'45'jmp'45'base_44 :: Integer
d_case'45'jmp'45'base_44 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.case-right-label-base
d_case'45'right'45'label'45'base_46 :: Integer
d_case'45'right'45'label'45'base_46 = coe (7 :: Integer)
-- Once.Backend.X86.CodeGen.curry-closure-instrs
d_curry'45'closure'45'instrs_48 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_curry'45'closure'45'instrs_48
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
               (coe (2 :: Integer)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_lea_62
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r9_28)
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_rip'43'disp_48
                  (coe (4 :: Integer))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r9_28)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_jmp_72 (coe (0 :: Integer)))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Once.Backend.X86.CodeGen.curry-closure-setup-count
d_curry'45'closure'45'setup'45'count_50 :: Integer
d_curry'45'closure'45'setup'45'count_50
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      d_curry'45'closure'45'instrs_48
-- Once.Backend.X86.CodeGen.curry-thunk-setup-len-calc
d_curry'45'thunk'45'setup'45'len'45'calc_52 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_curry'45'thunk'45'setup'45'len'45'calc_52
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_label_90
         (coe (6 :: Integer)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                  (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                     (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                        (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
                           (coe (2 :: Integer)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                           (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r12_34)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                              (coe
                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                                 (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                                 (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                              (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                              (coe
                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                 (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                              (coe
                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                 (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.Backend.X86.CodeGen.curry-thunk-cleanup
d_curry'45'thunk'45'cleanup_54 ::
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_curry'45'thunk'45'cleanup_54
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_ret_80)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.Backend.X86.Syntax.C_label_90
                     (coe (0 :: Integer)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.Backend.X86.CodeGen.curry-overhead
d_curry'45'overhead_56 :: Integer
d_curry'45'overhead_56
  = coe
      addInt
      (coe
         addInt
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            d_curry'45'thunk'45'cleanup_54)
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            d_curry'45'thunk'45'setup'45'len'45'calc_52))
      (coe d_curry'45'closure'45'setup'45'count_50)
-- Once.Backend.X86.CodeGen.curry-thunk-label
d_curry'45'thunk'45'label_58 :: Integer
d_curry'45'thunk'45'label_58
  = coe d_curry'45'closure'45'setup'45'count_50
-- Once.Backend.X86.CodeGen.curry-rip-offset
d_curry'45'rip'45'offset_60 :: Integer
d_curry'45'rip'45'offset_60 = coe (4 :: Integer)
-- Once.Backend.X86.CodeGen.curry-end-label-base
d_curry'45'end'45'label'45'base_62 :: Integer
d_curry'45'end'45'label'45'base_62
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 d_curry'45'overhead_56
      (1 :: Integer)
-- Once.Backend.X86.CodeGen.curry-jmp-base
d_curry'45'jmp'45'base_64 :: Integer
d_curry'45'jmp'45'base_64
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      d_curry'45'end'45'label'45'base_62
      d_curry'45'closure'45'setup'45'count_50
-- Once.Backend.X86.CodeGen.apply-consumed-slots
d_apply'45'consumed'45'slots_66 :: Integer
d_apply'45'consumed'45'slots_66
  = coe
      MAlonzo.Code.Once.Backend.X86.Syntax.d_instrs'45'consumed'45'slots_134
      d_apply'45'instrs_18
-- Once.Backend.X86.CodeGen.pair-setup-consumed-slots
d_pair'45'setup'45'consumed'45'slots_68 :: Integer
d_pair'45'setup'45'consumed'45'slots_68
  = coe
      MAlonzo.Code.Once.Backend.X86.Syntax.d_instrs'45'consumed'45'slots_134
      d_pair'45'setup_22
-- Once.Backend.X86.CodeGen.thunk-setup-consumed-slots
d_thunk'45'setup'45'consumed'45'slots_70 :: Integer
d_thunk'45'setup'45'consumed'45'slots_70
  = coe
      MAlonzo.Code.Once.Backend.X86.Syntax.d_instrs'45'consumed'45'slots_134
      d_curry'45'thunk'45'setup'45'len'45'calc_52
-- Once.Backend.X86.CodeGen.curry-closure-consumed-slots
d_curry'45'closure'45'consumed'45'slots_72 :: Integer
d_curry'45'closure'45'consumed'45'slots_72
  = coe
      MAlonzo.Code.Once.Backend.X86.Syntax.d_instrs'45'consumed'45'slots_134
      d_curry'45'closure'45'instrs_48
-- Once.Backend.X86.CodeGen.thunk-r15-slot
d_thunk'45'r15'45'slot_74 :: Integer
d_thunk'45'r15'45'slot_74 = coe (1 :: Integer)
-- Once.Backend.X86.CodeGen.thunk-rbp-slot
d_thunk'45'rbp'45'slot_76 :: Integer
d_thunk'45'rbp'45'slot_76 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.pair-r14-slot
d_pair'45'r14'45'slot_78 :: Integer
d_pair'45'r14'45'slot_78 = coe (1 :: Integer)
-- Once.Backend.X86.CodeGen.pair-r15-slot
d_pair'45'r15'45'slot_80 :: Integer
d_pair'45'r15'45'slot_80 = coe (2 :: Integer)
-- Once.Backend.X86.CodeGen.pair-rbp-slot
d_pair'45'rbp'45'slot_82 :: Integer
d_pair'45'rbp'45'slot_82 = coe (3 :: Integer)
-- Once.Backend.X86.CodeGen.compile-length
d_compile'45'length_88 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_compile'45'length_88 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             addInt
             (coe
                addInt (coe d_compile'45'length_88 (coe v0) (coe v4) (coe v7))
                (coe d_compile'45'length_88 (coe v4) (coe v1) (coe v6)))
             (coe d_simple'45'instr'45'count_8)
      MAlonzo.Code.Once.IR.C_fst_28 -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_snd_34 -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt (coe d_compile'45'length_88 (coe v0) (coe v9) (coe v6))
                       (coe d_compile'45'length_88 (coe v0) (coe v10) (coe v7)))
                    (coe d_pair'45'overhead_28)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5
        -> coe d_injection'45'instr'45'count_14
      MAlonzo.Code.Once.IR.C_inr_54 v5
        -> coe d_injection'45'instr'45'count_14
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt (coe d_compile'45'length_88 (coe v8) (coe v1) (coe v6))
                       (coe d_compile'45'length_88 (coe v9) (coe v1) (coe v7)))
                    (coe d_case'45'overhead_38)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_initial_70
        -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_curry_78 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> coe
                    addInt
                    (coe
                       d_compile'45'length_88
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v8))
                       (coe v10) (coe v6))
                    (coe d_curry'45'overhead_56)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84 -> coe d_apply'45'instr'45'count_20
      MAlonzo.Code.Once.IR.C_fold_88 -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_unfold_92
        -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_arr_98 -> coe d_simple'45'instr'45'count_8
      MAlonzo.Code.Once.IR.C_Prim_104 v5
        -> coe d_simple'45'instr'45'count_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.X86.CodeGen.case-cleanup-position
d_case'45'cleanup'45'position_110 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_case'45'cleanup'45'position_110 v0 v1 v2 v3 v4
  = coe
      addInt
      (coe
         addInt
         (coe
            addInt (coe d_compile'45'length_88 (coe v0) (coe v2) (coe v3))
            (coe d_compile'45'length_88 (coe v1) (coe v2) (coe v4)))
         (coe d_case'45'setup'45'prefix'45'count_40))
      (coe d_case'45'middle'45'count_34)
-- Once.Backend.X86.CodeGen.compile-x86
d_compile'45'x86_120 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  [MAlonzo.Code.Once.Backend.X86.Syntax.T_Instr_58]
d_compile'45'x86_120 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'x86_120 (coe v0) (coe v4) (coe v7))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                   (coe
                      MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                   (coe
                      MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe d_compile'45'x86_120 (coe v4) (coe v1) (coe v6))))
      MAlonzo.Code.Once.IR.C_fst_28
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                   (coe
                      MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_snd_34
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                   (coe
                      MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)
                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_pair'45'setup_22)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe d_compile'45'x86_120 (coe v0) (coe v9) (coe v6))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe d_pair'45'middle_24)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe d_compile'45'x86_120 (coe v0) (coe v10) (coe v7))
                             (coe d_pair'45'cleanup_26))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5 -> coe d_inl'45'instrs_10
      MAlonzo.Code.Once.IR.C_inr_54 v5 -> coe d_inr'45'instrs_12
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
                       (coe
                          MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                          (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                             (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                             (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r11_32))
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_cmp_68
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r11_32))
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_jne_76
                                   (coe
                                      addInt (coe d_compile'45'length_88 (coe v8) (coe v1) (coe v6))
                                      (coe d_case'45'jne'45'base_42)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                      (coe
                                         MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                         (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                                      (coe
                                         MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                         (coe
                                            MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                                            (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)
                                            (coe
                                               MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe d_compile'45'x86_120 (coe v8) (coe v1) (coe v6))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.X86.Syntax.C_jmp_72
                                            (coe
                                               addInt
                                               (coe
                                                  d_compile'45'length_88 (coe v9) (coe v1) (coe v7))
                                               (coe d_case'45'jmp'45'base_44)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.X86.Syntax.C_label_90
                                               (coe
                                                  addInt
                                                  (coe
                                                     d_compile'45'length_88 (coe v8) (coe v1)
                                                     (coe v6))
                                                  (coe d_case'45'right'45'label'45'base_46)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106))))
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                  (coe
                                                     d_compile'45'x86_120 (coe v9) (coe v1)
                                                     (coe v7))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                   (coe (0 :: Integer))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_initial_70
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_ud2_88)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_curry_78 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
                       (coe
                          MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                          (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                       (coe
                          MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
                             (coe (2 :: Integer)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                                (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                             (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Backend.X86.Syntax.C_lea_62
                             (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r9_28)
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_rip'43'disp_48
                                (coe d_curry'45'rip'45'offset_60)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                   (coe
                                      MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                                      (coe
                                         MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r9_28)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                   (coe
                                      MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                                   (coe
                                      MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                      (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.Backend.X86.Syntax.C_jmp_72
                                      (coe
                                         addInt
                                         (coe
                                            d_compile'45'length_88
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v8))
                                            (coe v10) (coe v6))
                                         (coe d_curry'45'jmp'45'base_64)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.Backend.X86.Syntax.C_label_90
                                         (coe d_curry'45'thunk'45'label_58))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
                                            (coe
                                               MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                               (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Backend.X86.Syntax.C_push_82
                                               (coe
                                                  MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Backend.X86.Syntax.C_sub_66
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_imm_56
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.d_slots_108
                                                           (coe (2 :: Integer)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_base_44
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_r12_34)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_mem_54
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_base'43'disp_46
                                                                 (coe
                                                                    MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Backend.X86.Syntax.d_slot'45'size_106)))
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                                 (coe
                                                                    MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20))
                                                              (coe
                                                                 MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                                 (coe
                                                                    MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24)))
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 d_compile'45'x86_120
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'42'__38
                                                                    (coe v0) (coe v8))
                                                                 (coe v10) (coe v6))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                                                                    (coe
                                                                       MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                                       (coe
                                                                          MAlonzo.Code.Once.Backend.X86.Syntax.C_rsp_24))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                                                                       (coe
                                                                          MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                                                                       (coe
                                                                          MAlonzo.Code.Once.Backend.X86.Syntax.C_rbp_22))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Backend.X86.Syntax.C_pop_84
                                                                          (coe
                                                                             MAlonzo.Code.Once.Backend.X86.Syntax.C_r15_40))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Backend.X86.Syntax.C_ret_80)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.Backend.X86.Syntax.C_label_90
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      d_compile'45'length_88
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Type.C__'42'__38
                                                                                         (coe v0)
                                                                                         (coe v8))
                                                                                      (coe v10)
                                                                                      (coe v6))
                                                                                   (coe
                                                                                      d_curry'45'end'45'label'45'base_62)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84 -> coe d_apply'45'instrs_18
      MAlonzo.Code.Once.IR.C_fold_88
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_unfold_92
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_arr_98
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.IR.C_Prim_104 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Backend.X86.Syntax.C_mov_60
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rax_10))
                (coe
                   MAlonzo.Code.Once.Backend.X86.Syntax.C_reg_52
                   (coe MAlonzo.Code.Once.Backend.X86.Syntax.C_rdi_20)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
