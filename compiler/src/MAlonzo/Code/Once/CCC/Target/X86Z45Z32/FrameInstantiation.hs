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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z32.FrameInstantiation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Layout
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Target.X86-32.FrameInstantiation.X86-32Frame
d_X86'45'32Frame_10 :: ()
d_X86'45'32Frame_10 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation._x86-32-≟F_
d__x86'45'32'45''8799'F__12 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__x86'45'32'45''8799'F__12
  = coe MAlonzo.Code.Once.Memory.StackSlots.du__'8799'SP__62
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-frame-base
d_x86'45'32'45'frame'45'base_14 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_x86'45'32'45'frame'45'base_14 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-addr
d_x86'45'32'45'slot'45'addr_16 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
d_x86'45'32'45'slot'45'addr_16 v0 v1
  = coe
      addInt (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth.d_word'45'size_10))
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-addr-eq
d_x86'45'32'45'slot'45'addr'45'eq_26 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'32'45'slot'45'addr'45'eq_26 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-zero-at-base
d_x86'45'32'45'slot'45'zero'45'at'45'base_34 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'32'45'slot'45'zero'45'at'45'base_34 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-addr-suc
d_x86'45'32'45'slot'45'addr'45'suc_46 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_x86'45'32'45'slot'45'addr'45'suc_46 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-injective
d_x86'45'32'45'slot'45'injective_64 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x86'45'32'45'slot'45'injective_64 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation._x86-32-≺_
d__x86'45'32'45''8826'__66 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> ()
d__x86'45'32'45''8826'__66 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-≺-trans
d_x86'45'32'45''8826''45'trans_78 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x86'45'32'45''8826''45'trans_78 ~v0 v1 ~v2 v3 v4
  = du_x86'45'32'45''8826''45'trans_78 v1 v3 v4
du_x86'45'32'45''8826''45'trans_78 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_x86'45'32'45''8826''45'trans_78 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe v1) (coe v2)
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-≺-irrefl
d_x86'45'32'45''8826''45'irrefl_92 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x86'45'32'45''8826''45'irrefl_92 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-≺-compare
d_x86'45'32'45''8826''45'compare_102 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_x86'45'32'45''8826''45'compare_102 v0 v1
  = let v2
          = MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0) in
    coe
      (let v3 = MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v1) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                         (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe
                          eqInt (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
                          (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v1)))
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                          (coe
                             eqInt (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
                             (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v1))))) in
          coe
            (case coe v4 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                 -> if coe v5
                      then coe
                             seq (coe v6)
                             (coe
                                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased))
                      else (let v7
                                  = seq
                                      (coe v6)
                                      (let v7
                                             = ltInt
                                                 (coe
                                                    MAlonzo.Code.Once.Memory.StackSlots.d_addr_20
                                                    (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Memory.StackSlots.d_addr_20
                                                    (coe v1)) in
                                       coe
                                         (if coe v7
                                            then coe
                                                   seq
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                      (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2824
                                                         (coe v2)))
                                            else coe
                                                   seq
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                      (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                                      (coe
                                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_3060
                                                         (coe v2)
                                                         (coe
                                                            MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_3044
                                                            (coe v2) (coe v3)))))) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v8
                                   -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v8)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v9
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v10
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v10))
                                 _ -> MAlonzo.RTE.mazUnreachableError))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-addr-mono-<
d_x86'45'32'45'slot'45'addr'45'mono'45''60'_136 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x86'45'32'45'slot'45'addr'45'mono'45''60'_136 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth.d_word'45'size_10)
         (coe v1) (coe v2) (coe v3))
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-frame-disjoint-bounded
d_x86'45'32'45'frame'45'disjoint'45'bounded_154 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x86'45'32'45'frame'45'disjoint'45'bounded_154 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation._.slot₂≥f₂
d_slot'8322''8805'f'8322'_174 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'8322''8805'f'8322'_174 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_slot'8322''8805'f'8322'_174 v1
du_slot'8322''8805'f'8322'_174 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'8322''8805'f'8322'_174 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Layout.du_slot'45'addr'45''8805''45'base_172
      (coe v0)
-- Once.CCC.Target.X86-32.FrameInstantiation._.slot₁<slot₂
d_slot'8321''60'slot'8322'_176 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'8321''60'slot'8322'_176 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_slot'8321''60'slot'8322'_176 v1 v5
du_slot'8321''60'slot'8322'_176 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'8321''60'slot'8322'_176 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v1) (coe du_slot'8322''8805'f'8322'_174 (coe v0))
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-slot-within-capacity-bound
d_x86'45'32'45'slot'45'within'45'capacity'45'bound_186 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x86'45'32'45'slot'45'within'45'capacity'45'bound_186 v0 ~v1 v2 v3
                                                       v4 v5
  = du_x86'45'32'45'slot'45'within'45'capacity'45'bound_186
      v0 v2 v3 v4 v5
du_x86'45'32'45'slot'45'within'45'capacity'45'bound_186 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_x86'45'32'45'slot'45'within'45'capacity'45'bound_186 v0 v1 v2 v3
                                                        v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe
         du_slot'60'cap'45'addr_204 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe v4)
-- Once.CCC.Target.X86-32.FrameInstantiation._.slot<cap-addr
d_slot'60'cap'45'addr_204 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'60'cap'45'addr_204 v0 ~v1 v2 v3 v4 ~v5
  = du_slot'60'cap'45'addr_204 v0 v2 v3 v4
du_slot'60'cap'45'addr_204 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'60'cap'45'addr_204 v0 v1 v2 v3
  = coe
      d_x86'45'32'45'slot'45'addr'45'mono'45''60'_136 (coe v0) (coe v1)
      (coe v2) (coe v3)
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-frame-disjoint-with-capacity
d_x86'45'32'45'frame'45'disjoint'45'with'45'capacity_216 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_x86'45'32'45'frame'45'disjoint'45'with'45'capacity_216 = erased
-- Once.CCC.Target.X86-32.FrameInstantiation._.slot-bound
d_slot'45'bound_238 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'bound_238 v0 ~v1 v2 ~v3 v4 ~v5 v6 v7
  = du_slot'45'bound_238 v0 v2 v4 v6 v7
du_slot'45'bound_238 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'bound_238 v0 v1 v2 v3 v4
  = coe
      du_x86'45'32'45'slot'45'within'45'capacity'45'bound_186 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-shift-frame
d_x86'45'32'45'shift'45'frame_240 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_x86'45'32'45'shift'45'frame_240 v0 v1
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
         (mulInt
            (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth.d_word'45'size_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z32.Layout.d_stack'45'sub'45'preserves''_158
         (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth.d_word'45'size_10))
         (coe
            MAlonzo.Code.Once.Memory.StackSlots.d_in'45'stack_22 (coe v0)))
-- Once.CCC.Target.X86-32.FrameInstantiation.x86-32-frame-semantics
d_x86'45'32'45'frame'45'semantics_246 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_250 ->
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_x86'45'32'45'frame'45'semantics_246 v0
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.C_constructor_152
      d__x86'45'32'45''8799'F__12 d_x86'45'32'45'frame'45'base_14
      d_x86'45'32'45'slot'45'addr_16 d_x86'45'32'45'shift'45'frame_240
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.StackGrowth.d_word'45'size_10
      (coe
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      MAlonzo.Code.Once.Float.Dyadic.d_binary32_40 v0
      (\ v1 v2 v3 ->
         coe
           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
           (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v2)))
      d_x86'45'32'45''8826''45'compare_102
