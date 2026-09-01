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

module MAlonzo.Code.Once.CCC.IR.Stack where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd

-- Once.CCC.IR.Stack.pair-slots
d_pair'45'slots_8 :: Integer
d_pair'45'slots_8 = coe (2 :: Integer)
-- Once.CCC.IR.Stack.closure-slots
d_closure'45'slots_10 :: Integer
d_closure'45'slots_10 = coe (2 :: Integer)
-- Once.CCC.IR.Stack.product-depth
d_product'45'depth_14 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 -> Integer
d_product'45'depth_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_118 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_120 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe d_product'45'depth_14 (coe v6) (coe v4))
                    (coe d_product'45'depth_14 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe d_product'45'depth_14 (coe v6) (coe v4))
                       (coe d_product'45'depth_14 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.sum-depth
d_sum'45'depth_26 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 -> Integer
d_sum'45'depth_26 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_118 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_120 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe d_sum'45'depth_26 (coe v6) (coe v4))
                       (coe d_sum'45'depth_26 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe d_sum'45'depth_26 (coe v6) (coe v4))
                    (coe d_sum'45'depth_26 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-requirement
d_ir'45'stack'45'requirement_40 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'requirement_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_22 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__30 v4 v6 v7
        -> coe
             addInt
             (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v4) (coe v7))
             (coe d_ir'45'stack'45'requirement_40 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v9) (coe v6)))
                       (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v10) (coe v7)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_50 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_inl_56 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_inr_62 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_case_70 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    addInt
                    (coe d_ir'45'stack'45'requirement_40 (coe v8) (coe v1) (coe v6))
                    (coe d_ir'45'stack'45'requirement_40 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_78 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_86 v6 v7 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_apply_92 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_In_96 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_Cata_108 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           addInt
                           (coe
                              addInt
                              (coe
                                 addInt
                                 (coe
                                    d_ir'45'stack'45'requirement_40
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v10)
                                          (coe v1)))
                                    (coe v1) (coe v7))
                                 (coe d_product'45'depth_14 (coe v10) (coe v4)))
                              (coe
                                 mulInt (coe d_sum'45'depth_26 (coe v10) (coe v4))
                                 (coe (2 :: Integer))))
                           (coe d_pair'45'slots_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_114 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             d_ir'45'stack'45'requirement_40
                             (coe
                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
                             (coe v1) (coe v6))
                          (coe d_product'45'depth_14 (coe v7) (coe v4)))
                       (coe
                          mulInt (coe d_sum'45'depth_26 (coe v7) (coe v4))
                          (coe (2 :: Integer))))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_118 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_in'45'ν_122 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_Ana_128 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement_40 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7) (coe v0))
                       (coe v6))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Hylo_136 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          d_ir'45'stack'45'requirement'45'nt_46 (coe v10) (coe v3) (coe v9))
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                          (coe v1) (coe v8)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Fuse_144 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          d_ir'45'stack'45'requirement'45'nt_46 (coe v10) (coe v3) (coe v9))
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v3) (coe v1))
                          (coe v1) (coe v8)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_free'45'heap_146 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_const_150 v4 v5 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_SigOp_156 v3 v4 v5 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-requirement-nt
d_ir'45'stack'45'requirement'45'nt_46 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IR.T_NatTr_18 -> Integer
d_ir'45'stack'45'requirement'45'nt_46 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_ntId_158 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_ntK_164 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_K_8 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_K_8 v7
                      -> coe d_ir'45'stack'45'requirement_40 (coe v6) (coe v7) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntFst_172 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v7) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntSnd_180 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v8) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntCase_188 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v8 v9
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v8) (coe v1) (coe v6))
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInl_196 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v7) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntInr_204 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v8) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_ntPair_212 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v8 v9
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v8) (coe v6))
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-scratch-requirement
d_ir'45'scratch'45'requirement_100 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'scratch'45'requirement_100 v0 v1
  = coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v1)
-- Once.CCC.IR.Stack.layer-capacity
d_layer'45'capacity_110 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_layer'45'capacity_110 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_118 v8
        -> coe
             addInt
             (coe
                d_ir'45'stack'45'requirement_40
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1) (coe v3)))
                (coe v3) (coe v6))
             (coe d_pair'45'slots_8)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_120
        -> coe
             d_ir'45'stack'45'requirement_40
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v1)))
             (coe v3) (coe MAlonzo.Code.Once.IR.C_Cata_108 v5 v6)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v11 v12
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe
                          d_layer'45'capacity_110 (coe v11) (coe v1) (coe v2) (coe v3)
                          (coe v9) (coe v5) (coe v6))
                       (coe
                          d_layer'45'capacity_110 (coe v12) (coe v1) (coe v2) (coe v3)
                          (coe v10) (coe v5) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v11 v12
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          d_layer'45'capacity_110 (coe v11) (coe v1) (coe v2) (coe v3)
                          (coe v9) (coe v5) (coe v6)))
                    (coe
                       d_layer'45'capacity_110 (coe v12) (coe v1) (coe v2) (coe v3)
                       (coe v10) (coe v5) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.∘-stack-req
d_'8728''45'stack'45'req_144 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8728''45'stack'45'req_144 = erased
-- Once.CCC.IR.Stack.⟨,⟩-stack-req
d_'10216''44''10217''45'stack'45'req_162 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''44''10217''45'stack'45'req_162 = erased
-- Once.CCC.IR.Stack.sigOp-stack-req
d_sigOp'45'stack'45'req_176 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigOp'45'stack'45'req_176 = erased
-- Once.CCC.IR.Stack.⟨,⟩-capacity-for-pair
d_'10216''44''10217''45'capacity'45'for'45'pair_194 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'capacity'45'for'45'pair_194 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 ~v7 v8
  = du_'10216''44''10217''45'capacity'45'for'45'pair_194 v8
du_'10216''44''10217''45'capacity'45'for'45'pair_194 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'capacity'45'for'45'pair_194 v0 = coe v0
-- Once.CCC.IR.Stack.layer-capacity-prod-left
d_layer'45'capacity'45'prod'45'left_252 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'left_252 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 ~v10 v11
  = du_layer'45'capacity'45'prod'45'left_252
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_layer'45'capacity'45'prod'45'left_252 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'left_252 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v9))
         (d_layer'45'capacity_110
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8))
         (addInt
            (coe
               d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8))
            (coe
               d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7) (coe v8)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8))))
      (coe v10)
-- Once.CCC.IR.Stack.layer-capacity-prod-right
d_layer'45'capacity'45'prod'45'right_304 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'right_304 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 ~v10 v11
  = du_layer'45'capacity'45'prod'45'right_304
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_layer'45'capacity'45'prod'45'right_304 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'right_304 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9 v10
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v9))
         (d_layer'45'capacity_110
            (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7) (coe v8))
         (addInt
            (coe
               d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v5) (coe v7) (coe v8))
            (coe
               d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7) (coe v8)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
            (coe
               d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7) (coe v8))))
      (coe v10)
-- Once.CCC.IR.Stack.layer-capacity-sum-left
d_layer'45'capacity'45'sum'45'left_356 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'left_356 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       v9 ~v10 v11
  = du_layer'45'capacity'45'sum'45'left_356
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_layer'45'capacity'45'sum'45'left_356 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'left_356 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v9
         (d_layer'45'capacity_110
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v7) (coe v8))
               (coe
                  d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7) (coe v8))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
               (coe
                  d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v7) (coe v8))
               (coe
                  d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7) (coe v8)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe v5) (coe v7) (coe v8))
                  (coe
                     d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                     (coe v6) (coe v7) (coe v8))))))
      (coe v10)
-- Once.CCC.IR.Stack.layer-capacity-sum-right
d_layer'45'capacity'45'sum'45'right_402 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'right_402 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 ~v10 v11
  = du_layer'45'capacity'45'sum'45'right_402
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v11
du_layer'45'capacity'45'sum'45'right_402 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'right_402 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9 v10
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v9
         (d_layer'45'capacity_110
            (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7) (coe v8))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v7) (coe v8))
               (coe
                  d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7) (coe v8))))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                  (coe
                     MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
               (coe
                  d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v5) (coe v7) (coe v8))
               (coe
                  d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7) (coe v8)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe v5) (coe v7) (coe v8))
                  (coe
                     d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
                     (coe v6) (coe v7) (coe v8))))))
      (coe v10)
-- Once.CCC.IR.Stack.sum-wrapper-fits-left
d_sum'45'wrapper'45'fits'45'left_444 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'left_444 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_110
         (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v7) (coe v8))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v7) (coe v8))
         (coe
            d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7) (coe v8)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
         (coe
            d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v7) (coe v8))
         (coe
            d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7) (coe v8)))
-- Once.CCC.IR.Stack.sum-wrapper-fits-right
d_sum'45'wrapper'45'fits'45'right_484 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'right_484 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_110
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7) (coe v8))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v7) (coe v8))
         (coe
            d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7) (coe v8)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'totalPreorder_2962))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8852''45'operator_4582))
         (coe
            d_layer'45'capacity_110 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v7) (coe v8))
         (coe
            d_layer'45'capacity_110 (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7) (coe v8)))
-- Once.CCC.IR.Stack.layer-cap-bound
d_layer'45'cap'45'bound_536 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'cap'45'bound_536 ~v0 v1 v2 v3 v4 v5 v6
  = du_layer'45'cap'45'bound_536 v1 v2 v3 v4 v5 v6
du_layer'45'cap'45'bound_536 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'cap'45'bound_536 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_118 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
             (coe
                addInt
                (coe
                   d_ir'45'stack'45'requirement_40
                   (coe
                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v0) (coe v2)))
                   (coe v2) (coe v5))
                (coe d_pair'45'slots_8))
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_120
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                d_layer'45'capacity_110 (coe MAlonzo.Code.Once.IRTy.C_Id_10)
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_126 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_132 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-req-geq-layer-cap
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_590 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_590 v0 v1 v2 v3 v4 v5
                                                ~v6 v7
  = du_ir'45'stack'45'req'45'geq'45'layer'45'cap_590
      v0 v1 v2 v3 v4 v5 v7
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_590 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_114 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_590 v0 v1 v2 v3 v4 v5
                                                 v6
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v5
         (d_layer'45'capacity_110
            (coe v0) (coe v0) (coe v1) (coe v2) (coe v3) (coe v3) (coe v4))
         (d_ir'45'stack'45'requirement_40
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
               (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v0)))
            (coe v2) (coe MAlonzo.Code.Once.IR.C_Cata_108 v3 v4))
         (coe
            du_layer'45'cap'45'bound_536 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v3) (coe v4)))
      (coe v6)
