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

module MAlonzo.Code.Once.CCC.Target.RiscV64.FrameInstantiation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.Layout
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Memory.StackSlots
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Target.RiscV64.FrameInstantiation.RV64Frame
d_RV64Frame_10 :: ()
d_RV64Frame_10 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.InStack-irrelevant
d_InStack'45'irrelevant_18 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_InStack'45'irrelevant_18 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._rv64-≟F_
d__rv64'45''8799'F__32 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__rv64'45''8799'F__32 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                   (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    eqInt (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
                    (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v1)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Target.RiscV64.FrameInstantiation._.sp-eq
d_sp'45'eq_60 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_60 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-frame-base
d_rv64'45'frame'45'base_66 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_rv64'45'frame'45'base_66 v0
  = coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0)
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-addr
d_rv64'45'slot'45'addr_68 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
d_rv64'45'slot'45'addr_68 v0 v1
  = coe
      addInt (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe
         mulInt (coe v1)
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10))
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-addr-eq
d_rv64'45'slot'45'addr'45'eq_78 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rv64'45'slot'45'addr'45'eq_78 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-zero-at-base
d_rv64'45'slot'45'zero'45'at'45'base_86 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rv64'45'slot'45'zero'45'at'45'base_86 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-addr-suc
d_rv64'45'slot'45'addr'45'suc_98 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rv64'45'slot'45'addr'45'suc_98 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-injective
d_rv64'45'slot'45'injective_116 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rv64'45'slot'45'injective_116 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._rv64-≺_
d__rv64'45''8826'__118 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> ()
d__rv64'45''8826'__118 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-≺-trans
d_rv64'45''8826''45'trans_130 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rv64'45''8826''45'trans_130 ~v0 v1 ~v2 v3 v4
  = du_rv64'45''8826''45'trans_130 v1 v3 v4
du_rv64'45''8826''45'trans_130 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rv64'45''8826''45'trans_130 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe v1) (coe v2)
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-≺-irrefl
d_rv64'45''8826''45'irrefl_144 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rv64'45''8826''45'irrefl_144 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-≺-compare
d_rv64'45''8826''45'compare_154 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_rv64'45''8826''45'compare_154 v0 v1
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
-- Once.CCC.Target.RiscV64.FrameInstantiation._.sp-eq
d_sp'45'eq_180 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sp'45'eq_180 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-addr-mono-<
d_rv64'45'slot'45'addr'45'mono'45''60'_198 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rv64'45'slot'45'addr'45'mono'45''60'_198 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'43''45'mono'691''45''60'_3714
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'42''45'mono'737''45''60'_4240
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10)
         (coe v1) (coe v2) (coe v3))
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-frame-disjoint-bounded
d_rv64'45'frame'45'disjoint'45'bounded_216 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rv64'45'frame'45'disjoint'45'bounded_216 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot₂≥f₂
d_slot'8322''8805'f'8322'_236 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'8322''8805'f'8322'_236 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_slot'8322''8805'f'8322'_236 v1
du_slot'8322''8805'f'8322'_236 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'8322''8805'f'8322'_236 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.Layout.du_slot'45'addr'45''8805''45'base_196
      (coe v0)
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot₁<slot₂
d_slot'8321''60'slot'8322'_238 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'8321''60'slot'8322'_238 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_slot'8321''60'slot'8322'_238 v1 v5
du_slot'8321''60'slot'8322'_238 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'8321''60'slot'8322'_238 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe v1) (coe du_slot'8322''8805'f'8322'_236 (coe v0))
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-slot-within-capacity-bound
d_rv64'45'slot'45'within'45'capacity'45'bound_248 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_rv64'45'slot'45'within'45'capacity'45'bound_248 v0 ~v1 v2 v3 v4
                                                  v5
  = du_rv64'45'slot'45'within'45'capacity'45'bound_248 v0 v2 v3 v4 v5
du_rv64'45'slot'45'within'45'capacity'45'bound_248 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_rv64'45'slot'45'within'45'capacity'45'bound_248 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3134
      (coe
         du_slot'60'cap'45'addr_266 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe v4)
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot<cap-addr
d_slot'60'cap'45'addr_266 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'60'cap'45'addr_266 v0 ~v1 v2 v3 v4 ~v5
  = du_slot'60'cap'45'addr_266 v0 v2 v3 v4
du_slot'60'cap'45'addr_266 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'60'cap'45'addr_266 v0 v1 v2 v3
  = coe
      d_rv64'45'slot'45'addr'45'mono'45''60'_198 (coe v0) (coe v1)
      (coe v2) (coe v3)
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-frame-disjoint-with-capacity
d_rv64'45'frame'45'disjoint'45'with'45'capacity_278 ::
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
d_rv64'45'frame'45'disjoint'45'with'45'capacity_278 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot-bound
d_slot'45'bound_300 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_slot'45'bound_300 v0 ~v1 v2 ~v3 v4 ~v5 v6 v7
  = du_slot'45'bound_300 v0 v2 v4 v6 v7
du_slot'45'bound_300 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_slot'45'bound_300 v0 v1 v2 v3 v4
  = coe
      du_rv64'45'slot'45'within'45'capacity'45'bound_248 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-shift-frame
d_rv64'45'shift'45'frame_302 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_rv64'45'shift'45'frame_302 v0 v1
  = coe
      MAlonzo.Code.Once.Memory.StackSlots.C_stack'45'addr_24
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
         (mulInt
            (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10)))
      (coe
         MAlonzo.Code.Once.CCC.Target.RiscV64.Layout.d_stack'45'sub'45'preserves''_182
         (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10))
         (coe
            MAlonzo.Code.Once.Memory.StackSlots.d_in'45'stack_22 (coe v0)))
-- Once.CCC.Target.RiscV64.FrameInstantiation.rv64-frame-semantics
d_rv64'45'frame'45'semantics_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6
d_rv64'45'frame'45'semantics_308
  = coe
      MAlonzo.Code.Once.CCC.FrameSemantics.C_constructor_152
      d__rv64'45''8799'F__32 d_rv64'45'frame'45'base_66
      d_rv64'45'slot'45'addr_68 d_rv64'45'shift'45'frame_302
      MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10
      MAlonzo.Code.Once.Float.Dyadic.d_binary64_42
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
           (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v1)))
      d_rv64'45''8826''45'compare_154
-- Once.CCC.Target.RiscV64.FrameInstantiation._._≺_
d__'8826'__326 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> ()
d__'8826'__326 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._._≟F_
d__'8799'F__328 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__328 = coe d__rv64'45''8799'F__32
-- Once.CCC.Target.RiscV64.FrameInstantiation._.Frame
d_Frame_330 :: ()
d_Frame_330 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.frame-base
d_frame'45'base_332 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 -> Integer
d_frame'45'base_332 = coe d_rv64'45'frame'45'base_66
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot-addr
d_slot'45'addr_334 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> Integer
d_slot'45'addr_334 = coe d_rv64'45'slot'45'addr_68
-- Once.CCC.Target.RiscV64.FrameInstantiation._.float-format
d_float'45'format_336 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28
d_float'45'format_336
  = coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_42
-- Once.CCC.Target.RiscV64.FrameInstantiation._.frame-disjoint-bounded
d_frame'45'disjoint'45'bounded_338 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_frame'45'disjoint'45'bounded_338 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.frame-word
d_frame'45'word_340 :: Integer
d_frame'45'word_340
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.StackGrowth.d_word'45'size_10
-- Once.CCC.Target.RiscV64.FrameInstantiation._.shift-base
d_shift'45'base_342 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'base_342 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.shift-frame
d_shift'45'frame_344 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14
d_shift'45'frame_344 = coe d_rv64'45'shift'45'frame_302
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot-addr-linear
d_slot'45'addr'45'linear_346 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'addr'45'linear_346 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot-injective
d_slot'45'injective_348 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_slot'45'injective_348 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.slot-zero-at-base
d_slot'45'zero'45'at'45'base_350 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_slot'45'zero'45'at'45'base_350 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.≺-compare
d_'8826''45'compare_352 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8826''45'compare_352 = coe d_rv64'45''8826''45'compare_154
-- Once.CCC.Target.RiscV64.FrameInstantiation._.≺-irrefl
d_'8826''45'irrefl_354 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8826''45'irrefl_354 = erased
-- Once.CCC.Target.RiscV64.FrameInstantiation._.≺-trans
d_'8826''45'trans_356 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8826''45'trans_356 ~v0 v1 ~v2 = du_'8826''45'trans_356 v1
du_'8826''45'trans_356 ::
  MAlonzo.Code.Once.Memory.StackSlots.T_StackAddr_14 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8826''45'trans_356 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe MAlonzo.Code.Once.Memory.StackSlots.d_addr_20 (coe v0))
