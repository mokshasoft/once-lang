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

module MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Memory.MemoryLayoutSemantics

-- Once.CCC.Target.RiscV64.StackGrowth.word-size
d_word'45'size_10 :: Integer
d_word'45'size_10 = coe (8 :: Integer)
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-grow
d_rv64'45'grow_12 :: Integer -> Integer -> Integer
d_rv64'45'grow_12 v0 v1
  = coe addInt (coe mulInt (coe v1) (coe d_word'45'size_10)) (coe v0)
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-grow-identity
d_rv64'45'grow'45'identity_20 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rv64'45'grow'45'identity_20 = erased
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-grow-injective
d_rv64'45'grow'45'injective_30 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rv64'45'grow'45'injective_30 = erased
-- Once.CCC.Target.RiscV64.StackGrowth._.cancel-*8
d_cancel'45''42'8_46 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cancel'45''42'8_46 = erased
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-grow-addr-injective
d_rv64'45'grow'45'addr'45'injective_56 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rv64'45'grow'45'addr'45'injective_56 = erased
-- Once.CCC.Target.RiscV64.StackGrowth.RV64FramePreserved
d_RV64FramePreserved_72 :: Integer -> Integer -> ()
d_RV64FramePreserved_72 = erased
-- Once.CCC.Target.RiscV64.StackGrowth.RV64StackGrew
d_RV64StackGrew_78 :: Integer -> Integer -> ()
d_RV64StackGrew_78 = erased
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-frame-preserved-under-growth
d_rv64'45'frame'45'preserved'45'under'45'growth_90 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rv64'45'frame'45'preserved'45'under'45'growth_90 ~v0 ~v1 ~v2 v3
                                                   v4
  = du_rv64'45'frame'45'preserved'45'under'45'growth_90 v3 v4
du_rv64'45'frame'45'preserved'45'under'45'growth_90 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rv64'45'frame'45'preserved'45'under'45'growth_90 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
      (coe v0)
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-slot-in-preserved-frame
d_rv64'45'slot'45'in'45'preserved'45'frame_108 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rv64'45'slot'45'in'45'preserved'45'frame_108 v0 ~v1 ~v2 v3
  = du_rv64'45'slot'45'in'45'preserved'45'frame_108 v0 v3
du_rv64'45'slot'45'in'45'preserved'45'frame_108 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rv64'45'slot'45'in'45'preserved'45'frame_108 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624 (coe v0))
-- Once.CCC.Target.RiscV64.StackGrowth.rv64-stack-growth
d_rv64'45'stack'45'growth_118 ::
  MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.T_StackGrowth_54
d_rv64'45'stack'45'growth_118
  = coe
      MAlonzo.Code.Once.Memory.MemoryLayoutSemantics.C_constructor_140
      d_rv64'45'grow_12
      (\ v0 v1 v2 v3 v4 ->
         coe du_rv64'45'frame'45'preserved'45'under'45'growth_90 v3 v4)
      (\ v0 v1 v2 v3 ->
         coe du_rv64'45'slot'45'in'45'preserved'45'frame_108 v0 v3)
