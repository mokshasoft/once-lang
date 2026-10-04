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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.FlatCorrespondence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
import qualified MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Memory.HeapAddress
import qualified MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.reg-of
d_reg'45'of_16 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
d_reg'45'of_16 ~v0 ~v1 = du_reg'45'of_16
du_reg'45'of_16 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8
du_reg'45'of_16
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'reg'45'of_10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.rreg
d_rreg_18 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
d_rreg_18 ~v0 ~v1 v2 v3 = du_rreg_18 v2 v3
du_rreg_18 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 -> Integer
du_rreg_18 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_readReg_240
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_388
         (coe v0))
      (coe v1)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.+-not-<
d_'43''45'not'45''60'_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''45'not'45''60'_26 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.AddrMap
d_AddrMap_28 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ExtDom
d_ExtDom_32 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr
d_FlatCorr_34 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.GapNext
d_GapNext_38 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_GapNext_38 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HDom
d_HDom_40 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_40 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView
d_HeapView_42 a0 a1 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Memory
d_Memory_46 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Memory_46 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.RetAddrs
d_RetAddrs_48 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [Integer] -> ()
d_RetAddrs_48 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles
d_Sets2Roles_50 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsMem
d_SetsMem_54 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRole
d_SetsRole_58 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem
d_SetsRoleMem_62 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.StackWindows
d_StackWindows_66 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_StackWindows_66 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Window
d_Window_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny -> Integer -> ()
d_Window_68 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Word
d_Word_70 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()
d_Word_70 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.amap
d_amap_72 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524
d_amap_72 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.C_mkAddrMap_534
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
         (coe v0))
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
         (coe v0))
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.at-addr
d_at'45'addr_74 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_74 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.at-role
d_at'45'role_76 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_76 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.at-role₁
d_at'45'role'8321'_78 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_78 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.at-role₂
d_at'45'role'8322'_80 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_80 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.atstack-frame-inj
d_atstack'45'frame'45'inj_82 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'frame'45'inj_82 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.atstack-slot-inj
d_atstack'45'slot'45'inj_84 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_atstack'45'slot'45'inj_84 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.caddr
d_caddr_86 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_86 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.clos-eq
d_clos'45'eq_88 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_88 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.cmap
d_cmap_90 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_90 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_532
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-regs-agree
d_corr'45'regs'45'agree_92 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_corr'45'regs'45'agree_92 ~v0 ~v1 = du_corr'45'regs'45'agree_92
du_corr'45'regs'45'agree_92 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_corr'45'regs'45'agree_92 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'regs'45'agree_4868
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.corr-store-gap
d_corr'45'store'45'gap_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_corr'45'store'45'gap_94 v0 ~v1 = du_corr'45'store'45'gap_94 v0
du_corr'45'store'45'gap_94 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (MAlonzo.Code.Once.Target.X86Z45Z64.PhysReg.T_Reg_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_corr'45'store'45'gap_94 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_corr'45'store'45'gap_4916
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v2 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.count-eq
d_count'45'eq_96 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_96 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dec-enc
d_dec'45'enc_98 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_98 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.descend-view
d_descend'45'view_100 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_descend'45'view_100 ~v0 ~v1 = du_descend'45'view_100
du_descend'45'view_100 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_descend'45'view_100 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_descend'45'view_1630
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dom-below
d_dom'45'below_102 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_102 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dom-fresh
d_dom'45'fresh_104 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_104 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1152
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dom-sized
d_dom'45'sized_106 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_106 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.dom-written
d_dom'45'written_108 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_108 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-ext
d_enc'45'ext_110 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext_110 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-ext-maybe
d_enc'45'ext'45'maybe_112 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'ext'45'maybe_112 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-maybe
d_enc'45'maybe_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe_114 v0 ~v1 = du_enc'45'maybe_114 v0
du_enc'45'maybe_114 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe_114 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe_580
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-maybe-at
d_enc'45'maybe'45'at_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
d_enc'45'maybe'45'at_116 v0 ~v1 = du_enc'45'maybe'45'at_116 v0
du_enc'45'maybe'45'at_116 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Maybe Integer
du_enc'45'maybe'45'at_116 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'maybe'45'at_564
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-sv
d_enc'45'sv_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv_118 v0 ~v1 = du_enc'45'sv_118 v0
du_enc'45'sv_118 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv_118 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv_576
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-sv-at
d_enc'45'sv'45'at_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
d_enc'45'sv'45'at_120 v0 ~v1 = du_enc'45'sv'45'at_120 v0
du_enc'45'sv'45'at_120 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 -> Integer
du_enc'45'sv'45'at_120 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_enc'45'sv'45'at_536
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.enc-zero
d_enc'45'zero_122 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_enc'45'zero_122 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-addr
d_ext'45'addr_124 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_ext'45'addr_124 ~v0 ~v1 = du_ext'45'addr_124
du_ext'45'addr_124 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
du_ext'45'addr_124
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr_3964
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-addr-aux
d_ext'45'addr'45'aux_126 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_ext'45'addr'45'aux_126 ~v0 ~v1 = du_ext'45'addr'45'aux_126
du_ext'45'addr'45'aux_126 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
du_ext'45'addr'45'aux_126 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ext'45'addr'45'aux_3946
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v0 v1 v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-addr-base
d_ext'45'addr'45'base_128 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'base_128 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-addr-fresh
d_ext'45'addr'45'fresh_130 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'fresh_130 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-addr-old
d_ext'45'addr'45'old_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'addr'45'old_132 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-suc
d_ext'45'suc_138 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc_138 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ext-suc-aux
d_ext'45'suc'45'aux_140 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapRef_8 ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'45'suc'45'aux_140 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.extend-view
d_extend'45'view_142 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
d_extend'45'view_142 ~v0 ~v1 = du_extend'45'view_142
du_extend'45'view_142 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464
du_extend'45'view_142 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_extend'45'view_4122
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v0 v1 v2 v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.frames-of
d_frames'45'of_144 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_frames'45'of_144 ~v0 ~v1 = du_frames'45'of_144
du_frames'45'of_144 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_frames'45'of_144
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_frames'45'of_584
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.front-lo
d_front'45'lo_146 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_146 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.frontier-eq
d_frontier'45'eq_148 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_148 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.haddr
d_haddr_150 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_150 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.haddr-inj
d_haddr'45'inj_152 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_152 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.haddr-suc
d_haddr'45'suc_154 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_154 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.halt-eq
d_halt'45'eq_156 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_156 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.heap-eq
d_heap'45'eq_158 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_158 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hfront
d_hfront_160 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_160 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.hmap
d_hmap_162 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_162 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_530
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.in1-eq
d_in1'45'eq_164 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_164 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.inc-enc
d_inc'45'enc_166 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inc'45'enc_166 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-clos
d_keep'45'clos_168 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'clos_168 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-count
d_keep'45'count_170 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'count_170 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-halt
d_keep'45'halt_172 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'halt_172 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-heap
d_keep'45'heap_174 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap_174 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-heap-reg
d_keep'45'heap'45'reg_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'heap'45'reg_176 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-in1
d_keep'45'in1_178 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'in1_178 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-lo-le
d_keep'45'lo'45'le_180 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_keep'45'lo'45'le_180 ~v0 ~v1 = du_keep'45'lo'45'le_180
du_keep'45'lo'45'le_180 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_keep'45'lo'45'le_180 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'lo'45'le_1278
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-out
d_keep'45'out_182 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'out_182 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-scratch
d_keep'45'scratch_184 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'scratch_184 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-sp
d_keep'45'sp_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'sp_186 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-stack
d_keep'45'stack_188 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_keep'45'stack_188 ~v0 ~v1 = du_keep'45'stack_188
du_keep'45'stack_188 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_keep'45'stack_188 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_keep'45'stack_1296
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keep-untouched
d_keep'45'untouched_190 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'untouched_190 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keeps-halt
d_keeps'45'halt_192 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_192 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keeps-halt₂
d_keeps'45'halt'8322'_194 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_194 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keeps-mem
d_keeps'45'mem_196 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_196 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.keeps-mem₂
d_keeps'45'mem'8322'_198 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_198 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.lit-word
d_lit'45'word_200 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_lit'45'word_200 ~v0 ~v1 v2 = du_lit'45'word_200 v2
du_lit'45'word_200 :: Integer -> Integer
du_lit'45'word_200 v0 = coe v0
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.lo
d_lo_202 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_202 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.lo-le
d_lo'45'le_204 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_204 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1168
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mem-halt
d_mem'45'halt_206 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_206 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mem-regs
d_mem'45'regs_208 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_208 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-clos
d_mkeep'45'clos_214 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'clos_214 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-count
d_mkeep'45'count_216 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'count_216 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-halt
d_mkeep'45'halt_218 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'halt_218 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-heap-reg
d_mkeep'45'heap'45'reg_220 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'heap'45'reg_220 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-in1
d_mkeep'45'in1_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'in1_222 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-lo-le
d_mkeep'45'lo'45'le_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mkeep'45'lo'45'le_224 ~v0 ~v1 = du_mkeep'45'lo'45'le_224
du_mkeep'45'lo'45'le_224 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_mkeep'45'lo'45'le_224 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_mkeep'45'lo'45'le_1380
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-out
d_mkeep'45'out_226 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'out_226 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-scratch
d_mkeep'45'scratch_228 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'scratch_228 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.mkeep-sp
d_mkeep'45'sp_230 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mkeep'45'sp_230 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.nz⇒pos
d_nz'8658'pos_232 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_nz'8658'pos_232 ~v0 ~v1 = du_nz'8658'pos_232
du_nz'8658'pos_232 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_nz'8658'pos_232 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_nz'8658'pos_58
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.off-addr
d_off'45'addr_234 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_234 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.off-role
d_off'45'role_236 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_236 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.off-roles
d_off'45'roles_238 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_238 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.out-eq
d_out'45'eq_240 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_240 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.read-write-hit
d_read'45'write'45'hit_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'hit_242 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.read-write-miss
d_read'45'write'45'miss_244 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_read'45'write'45'miss_244 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.readMem
d_readMem_246 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
d_readMem_246 ~v0 ~v1 = du_readMem_246
du_readMem_246 ::
  (Integer -> Maybe Integer) -> Integer -> Maybe Integer
du_readMem_246
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_readMem_66
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-agree-above
d_ret'45'agree'45'above_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'above_248 v0 ~v1
  = du_ret'45'agree'45'above_248 v0
du_ret'45'agree'45'above_248 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'above_248 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13 v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'above_4996
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v1 v7 v10 v11 v13 v14 v15
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-agree-nothing
d_ret'45'agree'45'nothing_250 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_ret'45'agree'45'nothing_250 ~v0 ~v1
  = du_ret'45'agree'45'nothing_250
du_ret'45'agree'45'nothing_250 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_ret'45'agree'45'nothing_250 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'agree'45'nothing_5352
      v8 v9 v11 v12
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-head
d_ret'45'head_252 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_ret'45'head_252 ~v0 ~v1 = du_ret'45'head_252
du_ret'45'head_252 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
du_ret'45'head_252 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'head_990
      v3 v9 v11
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-nil-frames
d_ret'45'nil'45'frames_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
d_ret'45'nil'45'frames_254 ~v0 ~v1 = du_ret'45'nil'45'frames_254
du_ret'45'nil'45'frames_254 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) -> [Integer] -> AgdaAny -> AgdaAny
du_ret'45'nil'45'frames_254 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'nil'45'frames_5452
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-relink
d_ret'45'relink_256 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_ret'45'relink_256 ~v0 ~v1 = du_ret'45'relink_256
du_ret'45'relink_256 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_ret'45'relink_256 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relink_798
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-relk
d_ret'45'relk_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_ret'45'relk_258 v0 ~v1 = du_ret'45'relk_258 v0
du_ret'45'relk_258 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer -> Integer -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_ret'45'relk_258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'relk_884
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v1 v5 v6 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-spill
d_ret'45'spill_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'spill_260 v0 ~v1 = du_ret'45'spill_260 v0
du_ret'45'spill_260 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  AgdaAny ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  AgdaAny ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'spill_260 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'spill_5506
      (coe v0) v11 v12 v13 v15
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-unlink
d_ret'45'unlink_262 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_ret'45'unlink_262 ~v0 ~v1 = du_ret'45'unlink_262
du_ret'45'unlink_262 ::
  (Integer -> Integer) ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_ret'45'unlink_262 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'unlink_712
      v0 v3 v7 v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.ret-write-in-frame
d_ret'45'write'45'in'45'frame_264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_ret'45'write'45'in'45'frame_264 v0 ~v1
  = du_ret'45'write'45'in'45'frame_264 v0
du_ret'45'write'45'in'45'frame_264 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  (Integer -> Integer) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Integer -> ()) ->
  (Integer -> Integer -> ()) ->
  Maybe Integer ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_ret'45'write'45'in'45'frame_264 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                   v10 v11 v12 v13 v14 v15 v16 v17 v18
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_ret'45'write'45'in'45'frame_5182
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v1 v6 v8 v11 v12 v13 v14 v15 v16 v17 v18
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.rm-at-addr
d_rm'45'at'45'addr_266 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_266 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.rm-at-role
d_rm'45'at'45'role_268 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_268 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.rm-halt
d_rm'45'halt_270 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_270 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.rm-off-addr
d_rm'45'off'45'addr_272 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_272 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.rm-off-role
d_rm'45'off'45'role_274 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_274 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.scratch-eq
d_scratch'45'eq_276 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_276 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sep
d_sep_278 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sep_278 ~v0 ~v1 = du_sep_278
du_sep_278 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_sep_278 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sep_1620
      v0 v3
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-alloc-heap
d_sim'45'alloc'45'heap_280 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'alloc'45'heap_280 ~v0 ~v1 = du_sim'45'alloc'45'heap_280
du_sim'45'alloc'45'heap_280 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> AgdaAny) ->
  (AgdaAny -> Integer -> AgdaAny) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'alloc'45'heap_280 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12 v13 v14
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'heap_4462
      v2 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-alloc-stack
d_sim'45'alloc'45'stack_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'alloc'45'stack_282 v0 ~v1
  = du_sim'45'alloc'45'stack_282 v0
du_sim'45'alloc'45'stack_282 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'alloc'45'stack_282 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                             v12 v13
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'alloc'45'stack_3344
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v2 v3 v6 v11
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-call-frame
d_sim'45'call'45'frame_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'call'45'frame_284 v0 ~v1 = du_sim'45'call'45'frame_284 v0
du_sim'45'call'45'frame_284 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'call'45'frame_284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                            v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'call'45'frame_3578
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'roles_12)
      (coe du_rreg_18) v3 v4 v6 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-dealloc-stack
d_sim'45'dealloc'45'stack_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'dealloc'45'stack_286 v0 ~v1
  = du_sim'45'dealloc'45'stack_286 v0
du_sim'45'dealloc'45'stack_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'dealloc'45'stack_286 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'dealloc'45'stack_3662
      (coe v0)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'roles_12)
      (coe du_rreg_18) v3 v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-heap-base
d_sim'45'heap'45'base_288 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'heap'45'base_288 ~v0 ~v1 = du_sim'45'heap'45'base_288
du_sim'45'heap'45'base_288 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'heap'45'base_288 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'heap'45'base_1700
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-lea-slot
d_sim'45'lea'45'slot_290 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'lea'45'slot_290 ~v0 ~v1 = du_sim'45'lea'45'slot_290
du_sim'45'lea'45'slot_290 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'lea'45'slot_290 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'lea'45'slot_4590
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-code-addr
d_sim'45'load'45'code'45'addr_292 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'code'45'addr_292 ~v0 ~v1
  = du_sim'45'load'45'code'45'addr_292
du_sim'45'load'45'code'45'addr_292 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'code'45'addr_292 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'code'45'addr_3818
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-const
d_sim'45'load'45'const_294 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'const_294 ~v0 ~v1 = du_sim'45'load'45'const_294
du_sim'45'load'45'const_294 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'const_294 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const_3764
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-const-float
d_sim'45'load'45'const'45'float_296 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'const'45'float_296 ~v0 ~v1
  = du_sim'45'load'45'const'45'float_296
du_sim'45'load'45'const'45'float_296 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'const'45'float_296 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'const'45'float_3790
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-from-slot
d_sim'45'load'45'from'45'slot_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'from'45'slot_298 ~v0 ~v1
  = du_sim'45'load'45'from'45'slot_298
du_sim'45'load'45'from'45'slot_298 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'from'45'slot_298 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'from'45'slot_2016
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-indirect
d_sim'45'load'45'indirect_300 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect_300 ~v0 ~v1
  = du_sim'45'load'45'indirect_300
du_sim'45'load'45'indirect_300 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect_300 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect_1962
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-indirect-stack
d_sim'45'load'45'indirect'45'stack_302 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'stack_302 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'stack_302
du_sim'45'load'45'indirect'45'stack_302 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'stack_302 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'stack_4632
      v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-indirect-suc
d_sim'45'load'45'indirect'45'suc_304 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'suc_304 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'suc_304
du_sim'45'load'45'indirect'45'suc_304 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'suc_304 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc_1908
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-indirect-suc-stack
d_sim'45'load'45'indirect'45'suc'45'stack_306 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'indirect'45'suc'45'stack_306 ~v0 ~v1
  = du_sim'45'load'45'indirect'45'suc'45'stack_306
du_sim'45'load'45'indirect'45'suc'45'stack_306 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'indirect'45'suc'45'stack_306 v0 v1 v2 v3 v4 v5 v6
                                               v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'indirect'45'suc'45'stack_4690
      v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-load-tag-lit
d_sim'45'load'45'tag'45'lit_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'load'45'tag'45'lit_308 ~v0 ~v1
  = du_sim'45'load'45'tag'45'lit_308
du_sim'45'load'45'tag'45'lit_308 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'load'45'tag'45'lit_308 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'load'45'tag'45'lit_1748
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-mov-to-input
d_sim'45'mov'45'to'45'input_310 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'mov'45'to'45'input_310 ~v0 ~v1
  = du_sim'45'mov'45'to'45'input_310
du_sim'45'mov'45'to'45'input_310 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'mov'45'to'45'input_310 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'input_1724
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-mov-to-output
d_sim'45'mov'45'to'45'output_312 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'mov'45'to'45'output_312 ~v0 ~v1
  = du_sim'45'mov'45'to'45'output_312
du_sim'45'mov'45'to'45'output_312 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'mov'45'to'45'output_312 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'mov'45'to'45'output_1678
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-out-nz
d_sim'45'out'45'nz_314 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'out'45'nz_314 ~v0 ~v1 = du_sim'45'out'45'nz_314
du_sim'45'out'45'nz_314 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'out'45'nz_314 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'out'45'nz_1774
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-count-inc
d_sim'45'reg'45'count'45'inc_316 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'count'45'inc_316 ~v0 ~v1
  = du_sim'45'reg'45'count'45'inc_316
du_sim'45'reg'45'count'45'inc_316 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'count'45'inc_316 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'inc_3890
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-count-zero
d_sim'45'reg'45'count'45'zero_318 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'count'45'zero_318 ~v0 ~v1
  = du_sim'45'reg'45'count'45'zero_318
du_sim'45'reg'45'count'45'zero_318 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'count'45'zero_318 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'count'45'zero_1846
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-scratch-dec
d_sim'45'reg'45'scratch'45'dec_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'dec_320 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'dec_320
du_sim'45'reg'45'scratch'45'dec_320 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'dec_320 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'dec_3920
      v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-scratch-load-count
d_sim'45'reg'45'scratch'45'load'45'count_322 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'load'45'count_322 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'load'45'count_322
du_sim'45'reg'45'scratch'45'load'45'count_322 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'load'45'count_322 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'load'45'count_1868
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-scratch-one
d_sim'45'reg'45'scratch'45'one_324 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'one_324 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'one_324
du_sim'45'reg'45'scratch'45'one_324 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'one_324 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'one_1802
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-reg-scratch-zero
d_sim'45'reg'45'scratch'45'zero_326 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'reg'45'scratch'45'zero_326 ~v0 ~v1
  = du_sim'45'reg'45'scratch'45'zero_326
du_sim'45'reg'45'scratch'45'zero_326 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'reg'45'scratch'45'zero_326 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'reg'45'scratch'45'zero_1824
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-restore-input
d_sim'45'restore'45'input_328 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'restore'45'input_328 ~v0 ~v1
  = du_sim'45'restore'45'input_328
du_sim'45'restore'45'input_328 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'restore'45'input_328 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'restore'45'input_2998
      v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-ret
d_sim'45'ret_330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'ret_330 v0 ~v1 = du_sim'45'ret_330 v0
du_sim'45'ret_330 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'ret_330 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'ret_3710
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      (coe
         MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'roles_12)
      (coe du_rreg_18) v2 v5 v6 v8
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-save-closure-reg
d_sim'45'save'45'closure'45'reg_332 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'save'45'closure'45'reg_332 ~v0 ~v1
  = du_sim'45'save'45'closure'45'reg_332
du_sim'45'save'45'closure'45'reg_332 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'save'45'closure'45'reg_332 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'save'45'closure'45'reg_3846
      v4
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-store-at-slot
d_sim'45'store'45'at'45'slot_334 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'at'45'slot_334 ~v0 ~v1
  = du_sim'45'store'45'at'45'slot_334
du_sim'45'store'45'at'45'slot_334 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'at'45'slot_334 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'at'45'slot_3290
      v2 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-store-indirect
d_sim'45'store'45'indirect_336 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect_336 ~v0 ~v1
  = du_sim'45'store'45'indirect_336
du_sim'45'store'45'indirect_336 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect_336 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect_2892
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-store-indirect-stack
d_sim'45'store'45'indirect'45'stack_338 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'stack_338 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'stack_338
du_sim'45'store'45'indirect'45'stack_338 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'stack_338 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'stack_4746
      v2 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-store-indirect-suc
d_sim'45'store'45'indirect'45'suc_340 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'suc_340 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'suc_340
du_sim'45'store'45'indirect'45'suc_340 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'suc_340 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc_2944
      v1 v2 v5 v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-store-indirect-suc-stack
d_sim'45'store'45'indirect'45'suc'45'stack_342 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'store'45'indirect'45'suc'45'stack_342 ~v0 ~v1
  = du_sim'45'store'45'indirect'45'suc'45'stack_342
du_sim'45'store'45'indirect'45'suc'45'stack_342 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'store'45'indirect'45'suc'45'stack_342 v0 v1 v2 v3 v4 v5
                                                v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'store'45'indirect'45'suc'45'stack_4808
      v2 v5
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sim-thunk
d_sim'45'thunk_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
d_sim'45'thunk_344 v0 ~v1 = du_sim'45'thunk_344 v0
du_sim'45'thunk_344 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084
du_sim'45'thunk_344 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_sim'45'thunk_3446
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v2 v3 v6 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-addr-inj
d_slot'45'addr'45'inj_346 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'inj_346 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-size>0
d_slot'45'size'62'0_348 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'size'62'0_348 ~v0 ~v1 = du_slot'45'size'62'0_348
du_slot'45'size'62'0_348 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'size'62'0_348
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'size'62'0_60
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slot-to-disp
d_slot'45'to'45'disp_350 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_slot'45'to'45'disp_350 ~v0 ~v1 = du_slot'45'to'45'disp_350
du_slot'45'to'45'disp_350 :: Integer -> Integer
du_slot'45'to'45'disp_350
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slot'45'to'45'disp_52
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.slots
d_slots_352 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> Integer
d_slots_352 ~v0 ~v1 = du_slots_352
du_slots_352 :: Integer -> Integer
du_slots_352
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_slots_48
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sp-eq
d_sp'45'eq_354 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_354 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stack-eq
d_stack'45'eq_356 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_356 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1174
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stack-eq-cur
d_stack'45'eq'45'cur_358 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'cur_358 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.stack-eq-win
d_stack'45'eq'45'win_360 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_stack'45'eq'45'win_360 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.store-dom-written
d_store'45'dom'45'written_362 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_store'45'dom'45'written_362 ~v0 ~v1
  = du_store'45'dom'45'written_362
du_store'45'dom'45'written_362 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_store'45'dom'45'written_362 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_store'45'dom'45'written_2292
      v1 v4 v5 v6 v7 v8
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.store-heap-eq
d_store'45'heap'45'eq_364 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  AgdaAny ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'heap'45'eq_364 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.store-slot-heap-eq
d_store'45'slot'45'heap'45'eq_366 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'heap'45'eq_366 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.store-slot-stack-eq
d_store'45'slot'45'stack'45'eq_368 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_store'45'slot'45'stack'45'eq_368 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.sv-tag-zero
d_sv'45'tag'45'zero_370 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sv'45'tag'45'zero_370 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.untouched
d_untouched_372 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_372 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.untouched-descend
d_untouched'45'descend_374 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'descend_374 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.untouched-heap-store
d_untouched'45'heap'45'store_376 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'heap'45'store_376 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.untouched-stack-store
d_untouched'45'stack'45'store_378 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'stack'45'store_378 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.untouched-write
d_untouched'45'write_380 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched'45'write_380 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.win-at
d_win'45'at_382 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'at_382 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.win-off
d_win'45'off_384 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_win'45'off_384 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.window-store-above
d_window'45'store'45'above_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_window'45'store'45'above_386 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-above
d_windows'45'above_388 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'above_388 ~v0 ~v1 = du_windows'45'above_388
du_windows'45'above_388 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'above_388 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'above_2602
      v6 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-enc-ext
d_windows'45'enc'45'ext_390 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
d_windows'45'enc'45'ext_390 ~v0 ~v1 = du_windows'45'enc'45'ext_390
du_windows'45'enc'45'ext_390 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
   AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny -> Integer -> AgdaAny) -> AgdaAny -> AgdaAny
du_windows'45'enc'45'ext_390 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'enc'45'ext_4380
      v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-forget
d_windows'45'forget_392 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
d_windows'45'forget_392 ~v0 ~v1 = du_windows'45'forget_392
du_windows'45'forget_392 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (AgdaAny ->
   Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> AgdaAny
du_windows'45'forget_392 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'forget_2482
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-heap-store
d_windows'45'heap'45'store_394 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'heap'45'store_394 ~v0 ~v1
  = du_windows'45'heap'45'store_394
du_windows'45'heap'45'store_394 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Machine.Flat.T_FlatState_68 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'heap'45'store_394 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'heap'45'store_2864
      v1 v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-leave
d_windows'45'leave_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'leave_396 v0 ~v1 = du_windows'45'leave_396 v0
du_windows'45'leave_396 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_504 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'leave_396 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'leave_2536
      (coe v0) v4 v6
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-lower
d_windows'45'lower_398 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'lower_398 ~v0 ~v1 = du_windows'45'lower_398
du_windows'45'lower_398 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'lower_398 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'lower_2436
      v5 v6 v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-reanchor
d_windows'45'reanchor_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'reanchor_400 ~v0 ~v1 = du_windows'45'reanchor_400
du_windows'45'reanchor_400 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'reanchor_400 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'reanchor_2406
      v8 v9
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-slot-store
d_windows'45'slot'45'store_402 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'slot'45'store_402 ~v0 ~v1
  = du_windows'45'slot'45'store_402
du_windows'45'slot'45'store_402 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_412 ->
  AgdaAny ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'slot'45'store_402 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11 v12
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'slot'45'store_3218
      v9 v12
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-store-gap
d_windows'45'store'45'gap_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_windows'45'store'45'gap_404 v0 ~v1
  = du_windows'45'store'45'gap_404 v0
du_windows'45'store'45'gap_404 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  (Integer -> Maybe Integer) ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  AgdaAny ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_windows'45'store'45'gap_404 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'store'45'gap_2726
      (coe v0)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.d_slot'45'size_86)
      v6 v7 v8 v10
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.windows-write-below
d_windows'45'write'45'below_406 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
d_windows'45'write'45'below_406 ~v0 ~v1
  = du_windows'45'write'45'below_406
du_windows'45'write'45'below_406 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  (AgdaAny ->
   Integer ->
   Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66) ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny -> AgdaAny
du_windows'45'write'45'below_406 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_windows'45'write'45'below_2816
      v7
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.writeMem
d_writeMem_408 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
d_writeMem_408 ~v0 ~v1 = du_writeMem_408
du_writeMem_408 ::
  (Integer -> Maybe Integer) ->
  Integer -> Integer -> Integer -> Maybe Integer
du_writeMem_408
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.du_writeMem_72
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.≡ᵇ-refl
d_'8801''7495''45'refl_410 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_410 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.≢→≡ᵇfalse
d_'8802''8594''8801''7495'false_412 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8594''8801''7495'false_412 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.AddrMap.cmap
d_cmap_416 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_cmap_416 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_cmap_532
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.AddrMap.hmap
d_hmap_418 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_AddrMap_524 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_hmap_418 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hmap_530
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.clos-eq
d_clos'45'eq_428 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clos'45'eq_428 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.count-eq
d_count'45'eq_430 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_count'45'eq_430 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.dom-fresh
d_dom'45'fresh_432 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'fresh_432 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'fresh_1152
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.dom-sized
d_dom'45'sized_434 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_dom'45'sized_434 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'sized_1162
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.dom-written
d_dom'45'written_436 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_StoredValue_66 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_dom'45'written_436 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'written_1158
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.frontier-eq
d_frontier'45'eq_438 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_frontier'45'eq_438 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.halt-eq
d_halt'45'eq_440 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'eq_440 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.heap-eq
d_heap'45'eq_442 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_heap'45'eq_442 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.in1-eq
d_in1'45'eq_444 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_in1'45'eq_444 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.lo-le
d_lo'45'le_446 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lo'45'le_446 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo'45'le_1168
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.out-eq
d_out'45'eq_448 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_out'45'eq_448 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.scratch-eq
d_scratch'45'eq_450 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scratch'45'eq_450 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.sp-eq
d_sp'45'eq_452 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_452 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.stack-eq
d_stack'45'eq_454 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stack'45'eq_454 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_stack'45'eq_1174
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.FlatCorr.untouched
d_untouched_456 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_FlatCorr_1084 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_untouched_456 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.HDom
d_HDom_460 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> ()
d_HDom_460 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.caddr
d_caddr_462 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer
d_caddr_462 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_caddr_498
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.dom-below
d_dom'45'below_464 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_dom'45'below_464 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_dom'45'below_512
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.front-lo
d_front'45'lo_466 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_front'45'lo_466 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_front'45'lo_516
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.haddr
d_haddr_468 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 -> Integer
d_haddr_468 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_haddr_492
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.haddr-inj
d_haddr'45'inj_470 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'inj_470 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.haddr-suc
d_haddr'45'suc_472 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  MAlonzo.Code.Once.Memory.HeapAddress.T_HeapLocation_42 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_haddr'45'suc_472 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.hfront
d_hfront_474 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_hfront_474 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_hfront_496
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.HeapView.lo
d_lo_476 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_HeapView_464 ->
  Integer
d_lo_476 v0
  = coe
      MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.d_lo_514
      (coe v0)
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles.at-role₁
d_at'45'role'8321'_480 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8321'_480 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles.at-role₂
d_at'45'role'8322'_482 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role'8322'_482 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles.keeps-halt₂
d_keeps'45'halt'8322'_484 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt'8322'_484 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles.keeps-mem₂
d_keeps'45'mem'8322'_486 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem'8322'_486 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.Sets2Roles.off-roles
d_off'45'roles_488 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'roles_488 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsMem.at-addr
d_at'45'addr_492 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'addr_492 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsMem.mem-halt
d_mem'45'halt_494 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'halt_494 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsMem.mem-regs
d_mem'45'regs_496 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mem'45'regs_496 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsMem.off-addr
d_off'45'addr_498 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'addr_498 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRole.at-role
d_at'45'role_502 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at'45'role_502 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRole.keeps-halt
d_keeps'45'halt_504 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'halt_504 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRole.keeps-mem
d_keeps'45'mem_506 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keeps'45'mem_506 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRole.off-role
d_off'45'role_508 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off'45'role_508 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem.rm-at-addr
d_rm'45'at'45'addr_512 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'addr_512 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem.rm-at-role
d_rm'45'at'45'role_514 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'at'45'role_514 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem.rm-halt
d_rm'45'halt_516 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'halt_516 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem.rm-off-addr
d_rm'45'off'45'addr_518 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'addr_518 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.SetsRoleMem.rm-off-role
d_rm'45'off'45'role_520 ::
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rm'45'off'45'role_520 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sets-role-x86
d_sets'45'role'45'x86_532 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRole_1186
d_sets'45'role'45'x86_532 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.at
d_at_550 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at_550 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.off
d_off_556 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_off_556 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sets-mem-x86
d_sets'45'mem'45'x86_582 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsMem_1308
d_sets'45'mem'45'x86_582 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sets-role-mem-x86
d_sets'45'role'45'mem'45'x86_614 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_SetsRoleMem_1396
d_sets'45'role'45'mem'45'x86_614 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence.sets-2roles-x86
d_sets'45'2roles'45'x86_648 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence.T_Sets2Roles_1452
d_sets'45'2roles'45'x86_648 = erased
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence._.s'
d_s''_670 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376
d_s''_670 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 v7 v8 ~v9
  = du_s''_670 v2 v3 v5 v7 v8
du_s''_670 ::
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376 ->
  MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.RegRoles.T_Role_10 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_Flags_360 ->
  Integer ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.T_State_376
du_s''_670 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.C_mkstate_398
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_writeReg_274
         (MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_regs_388
            (coe v0))
         (MAlonzo.Code.Once.Adequacy.ArchCorrectness.X86Z45Z64.RegRoles.d_x86'45'64'45'reg'45'of_10
            (coe v1))
         v2)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_memory_390
         (coe v0))
      (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Semantics.d_halted_396
         (coe v0))
