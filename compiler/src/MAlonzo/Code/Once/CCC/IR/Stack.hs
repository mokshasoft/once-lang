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
  MAlonzo.Code.Once.CCC.IR.T_IR_282 -> Integer
d_ir'45'stack'45'requirement_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CCC.IR.C_id_286 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C__'8728'__294 v4 v6 v7
        -> coe
             addInt
             (coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v4) (coe v7))
             (coe d_ir'45'stack'45'requirement_40 (coe v4) (coe v1) (coe v6))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_302 v6 v7 v8
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
      MAlonzo.Code.Once.CCC.IR.C_fst_308 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_snd_314 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_inl_320 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_inr_326 v5 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_case_334 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
               -> coe
                    addInt
                    (coe d_ir'45'stack'45'requirement_40 (coe v8) (coe v1) (coe v6))
                    (coe d_ir'45'stack'45'requirement_40 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_338 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_initial_342 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_curry_352 v7 v8 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_apply_360 -> coe d_pair'45'slots_8
      MAlonzo.Code.Once.CCC.IR.C_arr_368 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_In_372 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_376 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Cata_382 v4 v6
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
      MAlonzo.Code.Once.CCC.IR.C_Para_388 v4 v6
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
      MAlonzo.Code.Once.CCC.IR.C_Out_392 v4 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_396 v4 v5 -> coe (1 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_Ana_402 v4 v6
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
      MAlonzo.Code.Once.CCC.IR.C_Hylo_410 v3 v5 v6 v8 v9
        -> coe
             addInt
             (coe
                addInt
                (coe
                   d_ir'45'stack'45'requirement_40
                   (coe
                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                   (coe v1) (coe v8))
                (coe
                   d_ir'45'stack'45'requirement_40 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v0))
                   (coe v9)))
             (coe d_pair'45'slots_8)
      MAlonzo.Code.Once.CCC.IR.C_Fuse_418 v3 v5 v6 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v1))
                          (coe v1) (coe v8))
                       (coe
                          d_ir'45'stack'45'requirement_40
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v10) (coe v0))
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v3) (coe v0))
                          (coe v9)))
                    (coe d_pair'45'slots_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_420 v3
        -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_const_424 v4 v5 v6 -> coe (0 :: Integer)
      MAlonzo.Code.Once.CCC.IR.C_SigOp_430 v5 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-scratch-requirement
d_ir'45'scratch'45'requirement_76 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 -> Integer
d_ir'45'scratch'45'requirement_76 v0 v1
  = coe d_ir'45'stack'45'requirement_40 (coe v0) (coe v1)
-- Once.CCC.IR.Stack.layer-capacity
d_layer'45'capacity_84 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 -> Integer
d_layer'45'capacity_84 v0 v1 v2 v3 v4 v5
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
             (coe MAlonzo.Code.Once.CCC.IR.C_Cata_382 v4 v5)
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v10 v11
               -> coe
                    addInt (coe (2 :: Integer))
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe
                          d_layer'45'capacity_84 (coe v10) (coe v1) (coe v2) (coe v8)
                          (coe v4) (coe v5))
                       (coe
                          d_layer'45'capacity_84 (coe v11) (coe v1) (coe v2) (coe v9)
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
                          d_layer'45'capacity_84 (coe v10) (coe v1) (coe v2) (coe v8)
                          (coe v4) (coe v5)))
                    (coe
                       d_layer'45'capacity_84 (coe v11) (coe v1) (coe v2) (coe v9)
                       (coe v4) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.∘-stack-req
d_'8728''45'stack'45'req_118 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8728''45'stack'45'req_118 = erased
-- Once.CCC.IR.Stack.⟨,⟩-stack-req
d_'10216''44''10217''45'stack'45'req_136 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10216''44''10217''45'stack'45'req_136 = erased
-- Once.CCC.IR.Stack.sigOp-stack-req
d_sigOp'45'stack'45'req_150 ::
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_154 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sigOp'45'stack'45'req_150 = erased
-- Once.CCC.IR.Stack.⟨,⟩-capacity-for-pair
d_'10216''44''10217''45'capacity'45'for'45'pair_168 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_266 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'10216''44''10217''45'capacity'45'for'45'pair_168 ~v0 ~v1 ~v2 ~v3
                                                    ~v4 ~v5 ~v6 ~v7 v8
  = du_'10216''44''10217''45'capacity'45'for'45'pair_168 v8
du_'10216''44''10217''45'capacity'45'for'45'pair_168 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'10216''44''10217''45'capacity'45'for'45'pair_168 v0 = coe v0
-- Once.CCC.IR.Stack.layer-capacity-prod-left
d_layer'45'capacity'45'prod'45'left_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'left_224 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        ~v9 v10
  = du_layer'45'capacity'45'prod'45'left_224
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'prod'45'left_224 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'left_224 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v8))
         (d_layer'45'capacity_84
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
         (addInt
            (coe
               d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
               (coe v7))
            (coe
               d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
               (coe v7)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3624
            (coe
               d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
               (coe v7))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-prod-right
d_layer'45'capacity'45'prod'45'right_274 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'prod'45'right_274 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         ~v9 v10
  = du_layer'45'capacity'45'prod'45'right_274
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'prod'45'right_274 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'prod'45'right_274 v0 v1 v2 v3 v4 v5 v6 v7
                                          v8 v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         (addInt (coe (1 :: Integer)) (coe v8))
         (d_layer'45'capacity_84
            (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
         (addInt
            (coe
               d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
               (coe v7))
            (coe
               d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
               (coe v7)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
            (coe
               d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
               (coe v7))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-sum-left
d_layer'45'capacity'45'sum'45'left_324 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'left_324 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                       ~v9 v10
  = du_layer'45'capacity'45'sum'45'left_324
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'sum'45'left_324 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'left_324 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v8
         (d_layer'45'capacity_84
            (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                  (coe v7))
               (coe
                  d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                  (coe v7))))
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
                  d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                  (coe v7))
               (coe
                  d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                  (coe v7)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                     (coe v7))
                  (coe
                     d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                     (coe v7))))))
      (coe v9)
-- Once.CCC.IR.Stack.layer-capacity-sum-right
d_layer'45'capacity'45'sum'45'right_368 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'capacity'45'sum'45'right_368 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        ~v9 v10
  = du_layer'45'capacity'45'sum'45'right_368
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_layer'45'capacity'45'sum'45'right_368 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'capacity'45'sum'45'right_368 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                         v9
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v8
         (d_layer'45'capacity_84
            (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
         (addInt
            (coe (2 :: Integer))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
               (coe
                  d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                  (coe v7))
               (coe
                  d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                  (coe v7))))
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
                  d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                  (coe v7))
               (coe
                  d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                  (coe v7)))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'43'm_3636
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                  (coe
                     d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
                     (coe v7))
                  (coe
                     d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
                     (coe v7))))))
      (coe v9)
-- Once.CCC.IR.Stack.sum-wrapper-fits-left
d_sum'45'wrapper'45'fits'45'left_408 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'left_408 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_84
         (coe v0) (coe v2) (coe v3) (coe v4) (coe v6) (coe v7))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
            (coe v7))
         (coe
            d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
            (coe v7)))
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
            d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
            (coe v7))
         (coe
            d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
            (coe v7)))
-- Once.CCC.IR.Stack.sum-wrapper-fits-right
d_sum'45'wrapper'45'fits'45'right_446 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_sum'45'wrapper'45'fits'45'right_446 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'737''45''8804'_3682
      (2 :: Integer)
      (d_layer'45'capacity_84
         (coe v1) (coe v2) (coe v3) (coe v5) (coe v6) (coe v7))
      (MAlonzo.Code.Data.Nat.Base.d__'8852'__208
         (coe
            d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
            (coe v7))
         (coe
            d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
            (coe v7)))
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
            d_layer'45'capacity_84 (coe v0) (coe v2) (coe v3) (coe v4) (coe v6)
            (coe v7))
         (coe
            d_layer'45'capacity_84 (coe v1) (coe v2) (coe v3) (coe v5) (coe v6)
            (coe v7)))
-- Once.CCC.IR.Stack.layer-cap-bound
d_layer'45'cap'45'bound_494 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_layer'45'cap'45'bound_494 ~v0 v1 v2 v3 v4 v5
  = du_layer'45'cap'45'bound_494 v1 v2 v3 v4 v5
du_layer'45'cap'45'bound_494 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_layer'45'cap'45'bound_494 v0 v1 v2 v3 v4
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
                d_layer'45'capacity_84 (coe MAlonzo.Code.Once.Type.C_Id_116)
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.Machine.SMPrimitives.d_'33''33'_12 () erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.IR.Stack.ir-stack-req-geq-layer-cap
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_546 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_ir'45'stack'45'req'45'geq'45'layer'45'cap_546 v0 v1 v2 v3 v4 ~v5
                                                v6
  = du_ir'45'stack'45'req'45'geq'45'layer'45'cap_546
      v0 v1 v2 v3 v4 v6
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_546 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_282 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_ir'45'stack'45'req'45'geq'45'layer'45'cap_546 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'43''45'mono'691''45''8804'_3684
         v4
         (d_layer'45'capacity_84
            (coe v0) (coe v0) (coe v1) (coe v2) (coe v2) (coe v3))
         (d_ir'45'stack'45'requirement_40
            (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)
            (coe MAlonzo.Code.Once.CCC.IR.C_Cata_382 v2 v3))
         (coe
            du_layer'45'cap'45'bound_494 (coe v0) (coe v1) (coe v2) (coe v2)
            (coe v3)))
      (coe v5)
