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

module MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Target.RiscV64.PhysReg
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.fromℤ
d_fromℤ_12 :: Integer -> Integer
d_fromℤ_12
  = coe MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.IntW.modulus
d_modulus_14 :: Integer
d_modulus_14
  = coe
      MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.slot-to-disp
d_slot'45'to'45'disp_16 :: Integer -> Integer
d_slot'45'to'45'disp_16 v0
  = coe
      mulInt (coe v0)
      (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.room-code
d_room'45'code_20 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_room'45'code_20 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bgeu'45'fwd_38
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                  (coe
                     MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_local'45'1_40)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.fits-or-out
d_fits'45'or'45'out_24 ::
  Bool ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_fits'45'or'45'out_24 v0 v1
  = if coe v0
      then coe v1
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.room-fits?
d_room'45'fits'63'_28 :: Integer -> Bool
d_room'45'fits'63'_28 v0
  = coe
      ltInt
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Word.d_modulus_12 (coe (64 :: Integer)))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.out-code
d_out'45'code_36 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_out'45'code_36
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
            (coe
               MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.part
d_part_38 ::
  Bool ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_part_38 v0 v1 = if coe v0 then coe v1 else coe d_out'45'code_36
-- Once.CCC.Target.RiscV64.AbstractToRiscV.heap-room
d_heap'45'room_42 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_heap'45'room_42 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                  (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bgeu'45'fwd_38
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                        (coe
                           MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_local'45'1_40)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.stack-room
d_stack'45'room_46 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_stack'45'room_46 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                  (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bgeu'45'fwd_38
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                        (coe
                           MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_local'45'1_40)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.heap-code
d_heap'45'code_50 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_heap'45'code_50 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             d_part_38 (coe d_room'45'fits'63'_28 (coe v0))
             (coe d_heap'45'room_42 (coe v0))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.stack-code
d_stack'45'code_54 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_stack'45'code_54 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> coe
             d_part_38 (coe d_room'45'fits'63'_28 (coe v0))
             (coe d_stack'45'room_46 (coe v0))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.lower-room-c
d_lower'45'room'45'c_58 ::
  Bool ->
  Integer ->
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_lower'45'room'45'c_58 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                  (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v2)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_bgeu'45'fwd2_42
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        d_fits'45'or'45'out_24 (coe v0)
                        (coe d_room'45'code_20 (coe addInt (coe v1) (coe v2))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                           (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                           (coe
                              MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v2)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
                              (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                              (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                              (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
                                 (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                 (coe
                                    MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                                    (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                                    (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                                    (coe (0 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_local'45'2_44)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.lower-room
d_lower'45'room_66 ::
  Integer ->
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_lower'45'room_66 v0 v1
  = coe
      d_lower'45'room'45'c_58
      (coe d_room'45'fits'63'_28 (coe addInt (coe v0) (coe v1))) (coe v0)
      (coe v1)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.lower-out
d_lower'45'out_72 ::
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_lower'45'out_72
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
         (coe
            MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
            (coe
               MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'exhausted'45'symbol_170))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
               (coe
                  MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.lower-pick
d_lower'45'pick_74 ::
  Bool ->
  Integer ->
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_lower'45'pick_74 v0 v1 v2
  = if coe v0
      then coe d_lower'45'room_66 (coe v1) (coe v2)
      else coe d_lower'45'out_72
-- Once.CCC.Target.RiscV64.AbstractToRiscV.lower-code
d_lower'45'code_84 ::
  Integer ->
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_lower'45'code_84 v0 v1
  = coe
      d_lower'45'pick_74 (coe d_room'45'fits'63'_28 (coe v1)) (coe v0)
      (coe v1)
-- Once.CCC.Target.RiscV64.AbstractToRiscV.room-code′
d_room'45'code'8242'_90 ::
  Integer ->
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_room'45'code'8242'_90 v0 v1
  = case coe v1 of
      0 -> coe d_heap'45'code_50 (coe v0)
      _ -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_lower'45'code_84 (coe v0) (coe v1))
             (coe d_heap'45'code_50 (coe v0))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.start-tail
d_start'45'tail_98 ::
  Integer -> [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_start'45'tail_98 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
         (coe
            MAlonzo.Code.Data.Integer.Base.d_'45'__260
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
            (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.d_start'45'stack'45'words_2416)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sub_18
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
               (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
                  (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                  (coe
                     MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t2_46)
                     (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                     (coe (0 :: Integer)))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-abstract
d_compile'45'abstract_106 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430 ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_compile'45'abstract_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2432
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2434
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2436
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2438
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2440 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2442 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2444
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe (0 :: Integer)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2446
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2448 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2450 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'stack_2452 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'dealloc'45'stack_2454 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reclaim'45'to_2456 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'push'45'frame_2458 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe
                   MAlonzo.Code.Data.Integer.Base.d_'45'__260
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78)))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d_'45'__260
                            (coe
                               MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v1))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'pop'45'frame_2460
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe (0 :: Integer)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_fp_16)
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2462
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                   (coe
                      MAlonzo.Code.Data.Integer.Base.d_'45'__260
                      (coe
                         MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jalr_48
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                      (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                      (coe (0 :: Integer)))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'init_2464 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'push_2466 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'pop_2468 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_worklist'45'check_2470 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2476 v1 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                (coe
                   MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                   (coe MAlonzo.Code.Once.SigOp.Info.d_name_116 (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2482 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_fits'45'int_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                       (coe
                          MAlonzo.Code.Once.Spec.Word.d_fromℤ_22 (coe (64 :: Integer))
                          (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.Type.C_fits'45'float_28
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                       (coe
                          MAlonzo.Code.Once.Float.Word.d_round_58
                          (coe MAlonzo.Code.Once.Spec.Float.Dyadic.d_binary64_52) (coe v3)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2484 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla_28
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2486
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s1_34)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2488 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_li_24
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2490 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_mv_32
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_s2_36)
                   (coe
                      MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2492
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sltu_20
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2494 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2380 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_62
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2382 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_j_50
                       (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2384 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                       (coe (0 :: Integer)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_beq_34
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_zero_10)
                          (coe MAlonzo.Code.Once.CCC.Label.C_once_30 (coe v2)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2386 v2 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_label_62
                       (coe MAlonzo.Code.Once.CCC.Label.C_callee_34 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'45'__260
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v3))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                             (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                             (coe
                                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v3)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2388 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80 (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slots_80
                             (coe addInt (coe (1 :: Integer)) (coe v2))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ret_52)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2390 v2
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                       (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_sp_14)
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d_'45'__260
                          (coe
                             MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.d_slot'45'size_78)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_jal_46
                          (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_ra_12)
                          (coe
                             MAlonzo.Code.Once.CCC.Label.C_callee_34
                             (coe MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2392 v2
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_fits'45'or'45'out_24
                       (coe
                          d_room'45'fits'63'_28
                          (coe
                             addInt
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_start'45'stack'45'words_2416)
                             (coe v2)))
                       (coe
                          d_room'45'code_20
                          (coe
                             addInt
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.d_start'45'stack'45'words_2416)
                             (coe v2))))
                    (coe d_start'45'tail_98 (coe v2))
             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'leave_2394
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_call'45'sym_56
                       (coe
                          MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164))
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'free'45'heap_2496 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'room_2498 v1
        -> coe
             d_room'45'code'8242'_90
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45'h_2424 (coe v1))
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.d_room'45's_2426 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2500 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2502 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_addr'45'at_2504 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_addi_22
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t0_42)
                (coe d_slot'45'to'45'disp_16 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'rec_2506 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_ld_12
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                   (coe d_slot'45'to'45'disp_16 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'rec_2508 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_lla'45'sym_30
                (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                (coe
                   MAlonzo.Code.Once.Target.SymbolFresh.d_alloc'45'record'45'symbol_178))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.C_sd_14
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_a0_18)
                   (coe MAlonzo.Code.Once.Target.RiscV64.PhysReg.C_t1_44)
                   (coe d_slot'45'to'45'disp_16 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace
d_compile'45'trace_194 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  [MAlonzo.Code.Once.CCC.Target.RiscV64.Syntax.T_Instr_10]
d_compile'45'trace_194 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_compile'45'abstract_106 (coe v1))
             (coe d_compile'45'trace_194 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt
d_compile'45'trace'45'cnt_200 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compile'45'trace'45'cnt_200 ~v0 v1 v2
  = du_compile'45'trace'45'cnt_200 v1 v2
du_compile'45'trace'45'cnt_200 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compile'45'trace'45'cnt_200 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe du_compile'45'trace'45'cnt_200 (coe v0) (coe v3)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_compile'45'abstract_106 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe du_compile'45'trace'45'cnt_200 (coe v0) (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.RiscV64.AbstractToRiscV.compile-trace-cnt-agrees
d_compile'45'trace'45'cnt'45'agrees_224 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2430] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'trace'45'cnt'45'agrees_224 = erased
