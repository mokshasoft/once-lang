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
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.IR.Stack.pair-slots
d_pair'45'slots_8 :: Integer
d_pair'45'slots_8 = coe (2 :: Integer)
-- Once.CCC.IR.Stack.closure-slots
d_closure'45'slots_10 :: Integer
d_closure'45'slots_10 = coe (2 :: Integer)
-- Once.CCC.IR.Stack.product-depth
d_product'45'depth_14 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_product'45'depth_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe d_product'45'depth_14 (coe v6) (coe v4))
                    (coe d_product'45'depth_14 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v4 v5
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
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 -> Integer
d_sum'45'depth_26 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v3 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v6 v7
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe d_sum'45'depth_26 (coe v6) (coe v4))
                       (coe d_sum'45'depth_26 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v4 v5
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
      MAlonzo.Code.Once.IR.C_id_20 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             addInt
             (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v4) (coe v7))
             (coe d_ir'45'stack'45'requirement_40 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt (coe (1 :: Integer))
                          (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v8) (coe v6)))
                       (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v9) (coe v7)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_48 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_inl_54 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_inr_60 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    addInt
                    (coe d_ir'45'stack'45'requirement_40 (coe v8) (coe v1) (coe v6))
                    (coe d_ir'45'stack'45'requirement_40 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_76 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_84 v6 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_apply_90 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.IR.C_In_94 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
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
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v10)
                                          (coe v1)))
                                    (coe v1) (coe v7))
                                 (coe d_product'45'depth_14 (coe v10) (coe v4)))
                              (coe
                                 mulInt (coe d_sum'45'depth_26 (coe v10) (coe v4))
                                 (coe (2 :: Integer))))
                           (coe d_pair'45'slots_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4 -> coe (1 :: Integer)
      MAlonzo.Code.Once.IR.C_Ana_120 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement_40 (coe v0)
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v7) (coe v0))
                       (coe v6))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v4 v5 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_SigOp_130 v3 v4 v5 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_Call_136 v5 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-scratch-requirement
d_ir'45'scratch'45'requirement_64 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'scratch'45'requirement_64 v0 v1
  = coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v1)
-- Once.CCC.IR.Stack.∘-stack-req
d_'8728''45'stack'45'req_76 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8728''45'stack'45'req_76 = erased
-- Once.CCC.IR.Stack.⟨,⟩-stack-req
d_'10216''44''10217''45'stack'45'req_92 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''44''10217''45'stack'45'req_92 = erased
-- Once.CCC.IR.Stack.sigOp-stack-req
d_sigOp'45'stack'45'req_104 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigOp'45'stack'45'req_104 = erased
-- Once.CCC.IR.Stack.⟨,⟩-capacity-for-pair
d_'10216''44''10217''45'capacity'45'for'45'pair_120 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'capacity'45'for'45'pair_120 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 v7
  = du_'10216''44''10217''45'capacity'45'for'45'pair_120 v7
du_'10216''44''10217''45'capacity'45'for'45'pair_120 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'capacity'45'for'45'pair_120 v0 = coe v0
