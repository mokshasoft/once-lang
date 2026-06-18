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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.Machine.SMPrimitives
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Functor.Translate
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 -> Integer
d_product'45'depth_14 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe d_product'45'depth_14 (coe v6) (coe v4))
                    (coe d_product'45'depth_14 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v6 v7
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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 -> Integer
d_sum'45'depth_26 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v6 v7
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe d_sum'45'depth_26 (coe v6) (coe v4))
                       (coe d_sum'45'depth_26 (coe v7) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v6 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe d_sum'45'depth_26 (coe v6) (coe v4))
                    (coe d_sum'45'depth_26 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-requirement
d_ir'45'stack'45'requirement_40 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_ir'45'stack'45'requirement_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_280 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v4 v6 v7
        -> coe
             addInt
             (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v4) (coe v7))
             (coe d_ir'45'stack'45'requirement_40 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v9 v10
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
      MAlonzo.Code.Once.CCC.IR.C_fst_302 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_snd_308 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inl_314 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_inr_320 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_case_328 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    addInt
                    (coe d_ir'45'stack'45'requirement_40 (coe v8) (coe v1) (coe v6))
                    (coe d_ir'45'stack'45'requirement_40 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_332 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_initial_336 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_346 v7 v8 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_apply_354 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_arr_362 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_In_366 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Cata_376 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             d_ir'45'stack'45'requirement_40
                             (coe
                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v1))
                             (coe v1) (coe v6))
                          (coe d_product'45'depth_14 (coe v7) (coe v4)))
                       (coe
                          mulInt (coe d_sum'45'depth_26 (coe v7) (coe v4))
                          (coe (2 :: Integer))))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_382 v4 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v7
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          addInt
                          (coe
                             d_ir'45'stack'45'requirement_40
                             (coe
                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7)
                                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1)))
                             (coe v1) (coe v6))
                          (coe d_product'45'depth_14 (coe v7) (coe v4)))
                       (coe
                          mulInt (coe d_sum'45'depth_26 (coe v7) (coe v4))
                          (coe (2 :: Integer))))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Out_386 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_390 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Ana_396 v4 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_ν'45'type_134 v7
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement_40 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v7) (coe v0))
                       (coe v6))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          d_ir'45'stack'45'requirement'45'nt_46 (coe v10) (coe v3) (coe v9))
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                          (coe v1) (coe v8)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          d_ir'45'stack'45'requirement'45'nt_46 (coe v10) (coe v3) (coe v9))
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                          (coe v1) (coe v8)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_const_418 v4 v5 v6 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v5 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-requirement-nt
d_ir'45'stack'45'requirement'45'nt_46 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.CCC.IR.T_NatTr_276 -> Integer
d_ir'45'stack'45'requirement'45'nt_46 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_ntId_426 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_ntK_432 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v6
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_K_114 v7
                      -> coe d_ir'45'stack'45'requirement_40 (coe v6) (coe v7) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntFst_440 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v7) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntSnd_448 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v8) (coe v1) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntCase_456 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v8 v9
               -> coe
                    addInt
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v8) (coe v1) (coe v6))
                    (coe
                       d_ir'45'stack'45'requirement'45'nt_46 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInl_464 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v7) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntInr_472 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> coe
                    d_ir'45'stack'45'requirement'45'nt_46 (coe v0) (coe v8) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_ntPair_480 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v8 v9
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_ir'45'scratch'45'requirement_100 v0 v1
  = coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v1)
-- Once.CCC.IR.Stack.layer-capacity
d_layer'45'capacity_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_layer'45'capacity_108 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v7
        -> coe
             addInt
             (coe
                d_ir'45'stack'45'requirement_40
                (coe
                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v1) (coe v2))
                (coe v2) (coe v5))
             (coe d_pair'45'slots_8)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> coe
             d_ir'45'stack'45'requirement_40
             (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v1)) (coe v2)
             (coe MAlonzo.Code.Once.CCC.IR.C_Cata_376 v4 v5)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v10 v11
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe
                          d_layer'45'capacity_108 (coe v10) (coe v1) (coe v2) (coe v8)
                          (coe v4) (coe v5))
                       (coe
                          d_layer'45'capacity_108 (coe v11) (coe v1) (coe v2) (coe v9)
                          (coe v4) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v10 v11
               -> coe
                    addInt
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          d_layer'45'capacity_108 (coe v10) (coe v1) (coe v2) (coe v8)
                          (coe v4) (coe v5)))
                    (coe
                       d_layer'45'capacity_108 (coe v11) (coe v1) (coe v2) (coe v9)
                       (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.∘-stack-req
d_'8728''45'stack'45'req_142 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8728''45'stack'45'req_142 = erased
-- Once.CCC.IR.Stack.⟨,⟩-stack-req
d_'10216''44''10217''45'stack'45'req_160 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''44''10217''45'stack'45'req_160 = erased
-- Once.CCC.IR.Stack.sigOp-stack-req
d_sigOp'45'stack'45'req_174 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigOp'45'stack'45'req_174 = erased
-- Once.CCC.IR.Stack.⟨,⟩-capacity-for-pair
d_'10216''44''10217''45'capacity'45'for'45'pair_192 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'capacity'45'for'45'pair_192 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 ~v7 v8
  = du_'10216''44''10217''45'capacity'45'for'45'pair_192 v8
du_'10216''44''10217''45'capacity'45'for'45'pair_192 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'capacity'45'for'45'pair_192 v0 = coe v0
-- Once.CCC.IR.Stack.layer-capacity-prod-left
d_layer'45'capacity'45'prod'45'left_248 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'left_248 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        ~v9 v10
  = du_layer'45'capacity'45'prod'45'left_248
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'prod'45'left_248 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'left_248 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v8))
         (d_layer'45'capacity_108
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
         (addInt
            (coe
               d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7))
            (coe
               d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
               (coe v6) (coe v7)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-prod-right
d_layer'45'capacity'45'prod'45'right_298 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'right_298 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         ~v9 v10
  = du_layer'45'capacity'45'prod'45'right_298
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'prod'45'right_298 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'right_298 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v8))
         (d_layer'45'capacity_108
            (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
         (addInt
            (coe
               d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
               (coe v6) (coe v7))
            (coe
               d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
               (coe v6) (coe v7)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
            (coe
               d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
               (coe v6) (coe v7))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-sum-left
d_layer'45'capacity'45'sum'45'left_348 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'left_348 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       ~v9 v10
  = du_layer'45'capacity'45'sum'45'left_348
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'sum'45'left_348 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'left_348 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v8
         (d_layer'45'capacity_108
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7))
               (coe
                  d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                  (coe v6) (coe v7))))
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
                  d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7))
               (coe
                  d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                  (coe v6) (coe v7)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe v6) (coe v7))
                  (coe
                     d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                     (coe v6) (coe v7))))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-sum-right
d_layer'45'capacity'45'sum'45'right_392 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'right_392 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        ~v9 v10
  = du_layer'45'capacity'45'sum'45'right_392
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'sum'45'right_392 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'right_392 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v8
         (d_layer'45'capacity_108
            (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7))
               (coe
                  d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                  (coe v6) (coe v7))))
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
                  d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                  (coe v6) (coe v7))
               (coe
                  d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                  (coe v6) (coe v7)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
                     (coe v6) (coe v7))
                  (coe
                     d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
                     (coe v6) (coe v7))))))
      (coe v9)
-- Once.CCC.IR.Stack.sum-wrapper-fits-left
d_sum'45'wrapper'45'fits'45'left_432 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'left_432 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_108
         (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7))
         (coe
            d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
            (coe v6) (coe v7)))
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
            d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7))
         (coe
            d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
            (coe v6) (coe v7)))
-- Once.CCC.IR.Stack.sum-wrapper-fits-right
d_sum'45'wrapper'45'fits'45'right_470 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'right_470 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_108
         (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7))
         (coe
            d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
            (coe v6) (coe v7)))
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
            d_layer'45'capacity_108 (coe v0) (coe v2) (coe v3) (coe v4)
            (coe v6) (coe v7))
         (coe
            d_layer'45'capacity_108 (coe v1) (coe v2) (coe v3) (coe v5)
            (coe v6) (coe v7)))
-- Once.CCC.IR.Stack.layer-cap-bound
d_layer'45'cap'45'bound_518 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'cap'45'bound_518 ~v0 v1 v2 v3 v4 v5
  = du_layer'45'cap'45'bound_518 v1 v2 v3 v4 v5
du_layer'45'cap'45'bound_518 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'cap'45'bound_518 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v6
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
             (coe
                addInt
                (coe
                   d_ir'45'stack'45'requirement_40
                   (coe
                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                   (coe v1) (coe v4))
                (coe d_pair'45'slots_8))
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                d_layer'45'capacity_108 (coe MAlonzo.Code.Once.Type.C_Id_116)
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-req-geq-layer-cap
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_570 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_570 v0 v1 v2 v3 v4 ~v5
                                                v6
  = du_ir'45'stack'45'req'45'geq'45'layer'45'cap_570
      v0 v1 v2 v3 v4 v6
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_570 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_570 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v4
         (d_layer'45'capacity_108
            (coe v0) (coe v0) (coe v1) (coe v2) (coe v2) (coe v3))
         (d_ir'45'stack'45'requirement_40
            (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)
            (coe MAlonzo.Code.Once.CCC.IR.C_Cata_376 v2 v3))
         (coe
            du_layer'45'cap'45'bound_518 (coe v0) (coe v1) (coe v2) (coe v2)
            (coe v3)))
      (coe v5)
