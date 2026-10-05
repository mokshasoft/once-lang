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

module MAlonzo.Code.Once.CCC.Codegen.IRToTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Arith.CmpOp
import qualified MAlonzo.Code.Once.Arith.SigOp.Compare
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRToTrace.rec-count
d_rec'45'count_10 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
d_rec'45'count_10 ~v0 v1 = du_rec'45'count_10 v1
du_rec'45'count_10 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
du_rec'45'count_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C_Id_114 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe du_rec'45'count_10 (coe v1)) (coe du_rec'45'count_10 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             addInt (coe du_rec'45'count_10 (coe v1))
             (coe du_rec'45'count_10 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.CataStrategy
d_CataStrategy_20 a0 = ()
data T_CataStrategy_20
  = C_strat'45'const_22 | C_strat'45'nat_24 | C_strat'45'linear_26 |
    C_strat'45'branching_28 MAlonzo.Code.Once.Type.T_Functor_106
-- Once.CCC.Codegen.IRToTrace.has-id
d_has'45'id_30 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Bool
d_has'45'id_30 ~v0 v1 = du_has'45'id_30 v1
du_has'45'id_30 :: MAlonzo.Code.Once.Type.T_Functor_106 -> Bool
du_has'45'id_30 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_has'45'id_30 (coe v1)) (coe du_has'45'id_30 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_has'45'id_30 (coe v1)) (coe du_has'45'id_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.id-under-product
d_id'45'under'45'product_40 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Bool
d_id'45'under'45'product_40 ~v0 v1
  = du_id'45'under'45'product_40 v1
du_id'45'under'45'product_40 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> Bool
du_id'45'under'45'product_40 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_id'45'under'45'product_40 (coe v1))
             (coe du_id'45'under'45'product_40 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe du_has'45'id_30 (coe v1))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe du_has'45'id_30 (coe v2))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe du_id'45'under'45'product_40 (coe v1))
                   (coe du_id'45'under'45'product_40 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-strategy
d_cata'45'strategy_50 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> T_CataStrategy_20
d_cata'45'strategy_50 ~v0 v1 = du_cata'45'strategy_50 v1
du_cata'45'strategy_50 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> T_CataStrategy_20
du_cata'45'strategy_50 v0
  = let v1 = coe du_rec'45'count_10 (coe v0) in
    coe
      (case coe v1 of
         0 -> coe C_strat'45'const_22
         1 -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe du_id'45'under'45'product_40 (coe v0))
                (coe C_strat'45'linear_26) (coe C_strat'45'nat_24)
         _ -> coe C_strat'45'branching_28 (coe v0))
-- Once.CCC.Codegen.IRToTrace.cata-nat-layer
d_cata'45'nat'45'layer_64 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'nat'45'layer_64 ~v0 v1 v2
  = du_cata'45'nat'45'layer_64 v1 v2
du_cata'45'nat'45'layer_64 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_cata'45'nat'45'layer_64 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
            (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
               (coe (2 :: Integer)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe addInt (coe (1 :: Integer)) (coe v0)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                        (coe v1))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe v0))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (1 :: Integer)) (coe v0)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-nat-descend
d_cata'45'nat'45'descend_70 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'nat'45'descend_70 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
            (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                  (coe addInt (coe (1 :: Integer)) (coe v1)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                     (coe addInt (coe (2 :: Integer)) (coe v1)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (3 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                 (coe
                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                    (coe addInt (coe (2 :: Integer)) (coe v1)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_372))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                       (coe
                                          MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                          (coe addInt (coe (3 :: Integer)) (coe v1)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                          (coe
                                             MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                             (coe v1))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (1 :: Integer)) (coe v1)))))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-nat-I₁
d_cata'45'nat'45'I'8321'_74 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'nat'45'I'8321'_74 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_370))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_cata'45'nat'45'descend_70 (coe v0) (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe du_cata'45'nat'45'layer_64 (coe v1) (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Codegen.IRToTrace.cata-nat-I₂
d_cata'45'nat'45'I'8322'_80 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'nat'45'I'8322'_80 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
            (coe
               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
               (coe addInt (coe (4 :: Integer)) (coe v2)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                  (coe addInt (coe (5 :: Integer)) (coe v2)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe du_cata'45'nat'45'layer_64 (coe v1) (coe (1 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-nat-I₃
d_cata'45'nat'45'I'8323'_86 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'nat'45'I'8323'_86 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                  (coe addInt (coe (4 :: Integer)) (coe v1)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                     (coe addInt (coe (5 :: Integer)) (coe v1)))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.IRToTrace.cata-body
d_cata'45'body_90 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'body_90 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
            (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236
               (coe
                  MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24
                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v1)))
               (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 (coe v3)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                        (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-call-setup
d_cata'45'call'45'setup_100 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'call'45'setup_100 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
            (coe v3))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                     (coe (2 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                        (coe v4))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                              (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                             (coe (0 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                      (coe v5)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                         (coe v2))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-call
d_cata'45'call_112 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'call_112 ~v0 v1 v2 v3 = du_cata'45'call_112 v1 v2 v3
du_cata'45'call_112 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_cata'45'call_112 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
            (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
               (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                     (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe v0))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe v2))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-nat
d_cata'45'trace'45'nat_120 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'nat_120 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (6 :: Integer)) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (8 :: Integer)) (coe v3))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_100 (coe v0)
               (coe addInt (coe (2 :: Integer)) (coe v2))
               (coe addInt (coe (3 :: Integer)) (coe v2))
               (coe addInt (coe (4 :: Integer)) (coe v2))
               (coe addInt (coe (5 :: Integer)) (coe v2))
               (coe addInt (coe (6 :: Integer)) (coe v3)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe d_cata'45'nat'45'I'8321'_74 (coe v0) (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     du_cata'45'call_112 (coe addInt (coe (2 :: Integer)) (coe v2))
                     (coe addInt (coe (3 :: Integer)) (coe v2))
                     (coe addInt (coe (5 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe d_cata'45'nat'45'I'8322'_80 (coe v0) (coe v2) (coe v3))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           du_cata'45'call_112 (coe addInt (coe (2 :: Integer)) (coe v2))
                           (coe addInt (coe (3 :: Integer)) (coe v2))
                           (coe addInt (coe (5 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe d_cata'45'nat'45'I'8323'_86 (coe v0) (coe v3))
                           (coe
                              d_cata'45'body_90 (coe v0)
                              (coe addInt (coe (6 :: Integer)) (coe v3))
                              (coe addInt (coe (7 :: Integer)) (coe v3)) (coe v1)
                              (coe v4)))))))))
-- Once.CCC.Codegen.IRToTrace.cata-lin-I₁
d_cata'45'lin'45'I'8321'_130 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'lin'45'I'8321'_130 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'zero_378))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
            (coe (0 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (3 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                        (coe
                           MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                           (coe addInt (coe (1 :: Integer)) (coe v2)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                        (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_count'45'inc_380))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                    (coe addInt (coe (5 :: Integer)) (coe v1)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (2 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                             (coe (2 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (1 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                      (coe addInt (coe (5 :: Integer)) (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v1)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v1)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v1)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                        (coe
                                                                           addInt
                                                                           (coe (2 :: Integer))
                                                                           (coe v1)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                    (coe v0)
                                                                                    (coe v2))))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                                                       (coe v0)
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe
                                                                                             v2)))))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_376))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-lin-I₂
d_cata'45'lin'45'I'8322'_136 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'lin'45'I'8322'_136 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
            (coe
               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
               (coe addInt (coe (2 :: Integer)) (coe v2)))))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                  (coe addInt (coe (3 :: Integer)) (coe v2)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (4 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                  (coe addInt (coe (3 :: Integer)) (coe v1)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                           (coe addInt (coe (5 :: Integer)) (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                 (coe addInt (coe (3 :: Integer)) (coe v1)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                    (coe (2 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                       (coe addInt (coe (1 :: Integer)) (coe v1)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (5 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                   (coe addInt (coe (4 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                         (coe (2 :: Integer)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                            (coe v1))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                  (coe (1 :: Integer)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                        (coe
                                                                           addInt
                                                                           (coe (1 :: Integer))
                                                                           (coe v1)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                              (coe v1))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-lin-I₃
d_cata'45'lin'45'I'8323'_142 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'lin'45'I'8323'_142 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_374))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
               (coe
                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                  (coe addInt (coe (2 :: Integer)) (coe v1)))))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                     (coe addInt (coe (3 :: Integer)) (coe v1)))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.IRToTrace.cata-trace-linear
d_cata'45'trace'45'linear_146 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'linear_146 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (10 :: Integer)) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (6 :: Integer)) (coe v3))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_100 (coe v0)
               (coe addInt (coe (6 :: Integer)) (coe v2))
               (coe addInt (coe (7 :: Integer)) (coe v2))
               (coe addInt (coe (8 :: Integer)) (coe v2))
               (coe addInt (coe (9 :: Integer)) (coe v2))
               (coe addInt (coe (4 :: Integer)) (coe v3)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe d_cata'45'lin'45'I'8321'_130 (coe v0) (coe v2) (coe v3))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     du_cata'45'call_112 (coe addInt (coe (6 :: Integer)) (coe v2))
                     (coe addInt (coe (7 :: Integer)) (coe v2))
                     (coe addInt (coe (9 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe d_cata'45'lin'45'I'8322'_136 (coe v0) (coe v2) (coe v3))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           du_cata'45'call_112 (coe addInt (coe (6 :: Integer)) (coe v2))
                           (coe addInt (coe (7 :: Integer)) (coe v2))
                           (coe addInt (coe (9 :: Integer)) (coe v2)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe d_cata'45'lin'45'I'8323'_142 (coe v0) (coe v3))
                           (coe
                              d_cata'45'body_90 (coe v0)
                              (coe addInt (coe (4 :: Integer)) (coe v3))
                              (coe addInt (coe (5 :: Integer)) (coe v3)) (coe v1)
                              (coe v4)))))))))
-- Once.CCC.Codegen.IRToTrace.fsize
d_fsize_156 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
d_fsize_156 ~v0 v1 = du_fsize_156 v1
du_fsize_156 :: MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
du_fsize_156 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Id_114 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             addInt
             (coe addInt (coe (1 :: Integer)) (coe du_fsize_156 (coe v1)))
             (coe du_fsize_156 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             addInt
             (coe addInt (coe (1 :: Integer)) (coe du_fsize_156 (coe v1)))
             (coe du_fsize_156 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.push2
d_push2_172 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_push2_172 ~v0 v1 v2 v3 = du_push2_172 v1 v2 v3
du_push2_172 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_push2_172 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                     (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe v0))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                    (coe v0))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.pop2
d_pop2_182 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_pop2_182 ~v0 v1 = du_pop2_182 v1
du_pop2_182 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_pop2_182 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
         (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.wrap-sum
d_wrap'45'sum_190 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_wrap'45'sum_190 ~v0 v1 v2 = du_wrap'45'sum_190 v1 v2
du_wrap'45'sum_190 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_wrap'45'sum_190 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (1 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                     (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Once.CCC.Codegen.IRToTrace.lsize
d_lsize_196 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
d_lsize_196 ~v0 v1 = du_lsize_196 v1
du_lsize_196 :: MAlonzo.Code.Once.Type.T_Functor_106 -> Integer
du_lsize_196 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C_Id_114 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C__'8853'__116 v1 v2
        -> coe
             addInt
             (coe addInt (coe (2 :: Integer)) (coe du_lsize_196 (coe v1)))
             (coe du_lsize_196 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__118 v1 v2
        -> coe
             addInt (coe du_lsize_196 (coe v1)) (coe du_lsize_196 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.visit-walk
d_visit'45'walk_216 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_visit'45'walk_216 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Type.C_K_112 v7
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_Id_114
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
             (coe du_push2_172 (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_visit'45'walk_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                   (coe addInt (coe (4 :: Integer)) (coe v5))
                   (coe
                      addInt
                      (coe addInt (coe (2 :: Integer)) (coe du_lsize_196 (coe v7)))
                      (coe v6)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                            (coe
                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                               (coe addInt (coe (1 :: Integer)) (coe v6)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                               (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v6))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         d_visit'45'walk_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                         (coe addInt (coe (4 :: Integer)) (coe v5))
                         (coe addInt (coe (2 :: Integer)) (coe v6)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v6)))))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                      (coe v5))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_visit'45'walk_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                   (coe addInt (coe (4 :: Integer)) (coe v5)) (coe v6))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                         (coe v5))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      d_visit'45'walk_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                      (coe addInt (coe (4 :: Integer)) (coe v5))
                      (coe addInt (coe du_lsize_196 (coe v7)) (coe v6)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.rebuild-walk
d_rebuild'45'walk_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_rebuild'45'walk_276 v0 v1 ~v2 ~v3 v4 v5 v6
  = du_rebuild'45'walk_276 v0 v1 v4 v5 v6
du_rebuild'45'walk_276 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_rebuild'45'walk_276 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_K_112 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_Id_114 -> coe du_pop2_182 (coe v1)
      MAlonzo.Code.Once.Type.C__'8853'__116 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_rebuild'45'walk_276 (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe
                      addInt
                      (coe addInt (coe (2 :: Integer)) (coe du_lsize_196 (coe v5)))
                      (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe du_wrap'45'sum_190 (coe (1 :: Integer)) (coe v3))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                               (coe
                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                  (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe
                            du_rebuild'45'walk_276 (coe v0) (coe v1) (coe v5)
                            (coe addInt (coe (4 :: Integer)) (coe v3))
                            (coe addInt (coe (2 :: Integer)) (coe v4)))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                            (coe du_wrap'45'sum_190 (coe (0 :: Integer)) (coe v3))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                     (coe
                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                        (coe addInt (coe (1 :: Integer)) (coe v4)))))
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
      MAlonzo.Code.Once.Type.C__'8855'__118 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                      (coe v3))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_rebuild'45'walk_276 (coe v0) (coe v1) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v3))
                   (coe addInt (coe du_lsize_196 (coe v5)) (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                         (coe addInt (coe (2 :: Integer)) (coe v3)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_276 (coe v0) (coe v1) (coe v5)
                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe addInt (coe (1 :: Integer)) (coe v3)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                  (coe addInt (coe (3 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                        (coe addInt (coe (1 :: Integer)) (coe v3)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                              (coe addInt (coe (2 :: Integer)) (coe v3)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                    (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-br-I₁
d_cata'45'br'45'I'8321'_326 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'br'45'I'8321'_326 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe addInt (coe (3 :: Integer)) (coe v2)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (6 :: Integer)) (coe v2)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                 (coe addInt (coe (6 :: Integer)) (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (6 :: Integer)) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (2 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (6 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                   (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            du_push2_172 (coe v2) (coe addInt (coe (4 :: Integer)) (coe v2))
            (coe addInt (coe (5 :: Integer)) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                     (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                     (coe v2))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                              (coe
                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                 (coe addInt (coe (1 :: Integer)) (coe v3)))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe addInt (coe (3 :: Integer)) (coe v2)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                             (coe addInt (coe (3 :: Integer)) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_push2_172 (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (4 :: Integer)) (coe v2))
                  (coe addInt (coe (5 :: Integer)) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                        (coe addInt (coe (3 :: Integer)) (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        d_visit'45'walk_216 (coe v0) (coe v2)
                        (coe addInt (coe (4 :: Integer)) (coe v2))
                        (coe addInt (coe (5 :: Integer)) (coe v2)) (coe v1)
                        (coe addInt (coe (7 :: Integer)) (coe v2))
                        (coe addInt (coe (4 :: Integer)) (coe v3)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                 (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (1 :: Integer)) (coe v3)))))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                    (coe
                                       MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                       (coe addInt (coe (2 :: Integer)) (coe v3)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                    (coe addInt (coe (1 :: Integer)) (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                             (coe
                                                MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                (coe addInt (coe (3 :: Integer)) (coe v3)))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 du_rebuild'45'walk_276 (coe v0)
                                 (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v1)
                                 (coe addInt (coe (7 :: Integer)) (coe v2))
                                 (coe
                                    addInt
                                    (coe addInt (coe (4 :: Integer)) (coe du_lsize_196 (coe v1)))
                                    (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-br-I₂
d_cata'45'br'45'I'8322'_334 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cata'45'br'45'I'8322'_334 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         du_push2_172 (coe addInt (coe (2 :: Integer)) (coe v1))
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe addInt (coe (5 :: Integer)) (coe v1)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                  (coe
                     MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                     (coe addInt (coe (2 :: Integer)) (coe v2)))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                     (coe
                        MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                        (coe addInt (coe (3 :: Integer)) (coe v2)))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
               (coe addInt (coe (2 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-branching
d_cata'45'trace'45'branching_340 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_340 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            addInt (coe (15 :: Integer))
            (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
         (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt
            (coe
               addInt
               (coe addInt (coe (6 :: Integer)) (coe du_lsize_196 (coe v1)))
               (coe du_lsize_196 (coe v1)))
            (coe v4))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_100 (coe v0)
               (coe
                  addInt
                  (coe
                     addInt (coe (11 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt (coe (12 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt (coe (13 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt (coe (14 :: Integer))
                     (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                  (coe v3))
               (coe
                  addInt
                  (coe
                     addInt
                     (coe addInt (coe (4 :: Integer)) (coe du_lsize_196 (coe v1)))
                     (coe du_lsize_196 (coe v1)))
                  (coe v4)))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  d_cata'45'br'45'I'8321'_326 (coe v0) (coe v1) (coe v3) (coe v4))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     du_cata'45'call_112
                     (coe
                        addInt
                        (coe
                           addInt (coe (11 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                        (coe v3))
                     (coe
                        addInt
                        (coe
                           addInt (coe (12 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                        (coe v3))
                     (coe
                        addInt
                        (coe
                           addInt (coe (14 :: Integer))
                           (coe mulInt (coe (4 :: Integer)) (coe du_fsize_156 (coe v1))))
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe d_cata'45'br'45'I'8322'_334 (coe v0) (coe v3) (coe v4))
                     (coe
                        d_cata'45'body_90 (coe v0)
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (4 :: Integer)) (coe du_lsize_196 (coe v1)))
                              (coe du_lsize_196 (coe v1)))
                           (coe v4))
                        (coe
                           addInt
                           (coe
                              addInt
                              (coe addInt (coe (5 :: Integer)) (coe du_lsize_196 (coe v1)))
                              (coe du_lsize_196 (coe v1)))
                           (coe v4))
                        (coe v2) (coe v5)))))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-const
d_cata'45'trace'45'const_352 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'const_352 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (4 :: Integer)) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (2 :: Integer)) (coe v3))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               d_cata'45'call'45'setup_100 (coe v0) (coe v2)
               (coe addInt (coe (1 :: Integer)) (coe v2))
               (coe addInt (coe (2 :: Integer)) (coe v2))
               (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  du_cata'45'call_112 (coe v2)
                  (coe addInt (coe (1 :: Integer)) (coe v2))
                  (coe addInt (coe (3 :: Integer)) (coe v2)))
               (coe
                  d_cata'45'body_90 (coe v0) (coe v3)
                  (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v1) (coe v4)))))
-- Once.CCC.Codegen.IRToTrace.cata-dispatch
d_cata'45'dispatch_362 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  T_CataStrategy_20 ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_362 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      C_strat'45'const_22
        -> coe
             d_cata'45'trace'45'const_352 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      C_strat'45'nat_24
        -> coe
             d_cata'45'trace'45'nat_120 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      C_strat'45'linear_26
        -> coe
             d_cata'45'trace'45'linear_146 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
      C_strat'45'branching_28 v6
        -> coe
             d_cata'45'trace'45'branching_340 (coe v0) (coe v6) (coe v2)
             (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.resuspend-layer
d_resuspend'45'layer_400 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resuspend'45'layer_400 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.IRTy.C_wf'45'K_126 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.IRTy.C_wf'45'Id_128
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (4 :: Integer)) (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                      (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                         (coe (2 :: Integer)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe addInt (coe (1 :: Integer)) (coe v1)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                               (coe v4))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                    (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                       (coe (2 :: Integer)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                          (coe
                                                             addInt (coe (3 :: Integer)) (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                (coe
                                                                   addInt (coe (2 :: Integer))
                                                                   (coe v1)))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                                      (coe v3))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                            (coe
                                                                               addInt
                                                                               (coe (3 :: Integer))
                                                                               (coe v1)))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))))
      MAlonzo.Code.Once.IRTy.C_wf'45'Sum_134 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8853'__12 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_400 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_400 (coe v0)
                                (coe addInt (coe (3 :: Integer)) (coe v1))
                                (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_400 (coe v0)
                                   (coe addInt (coe (3 :: Integer)) (coe v1))
                                   (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                   (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_400 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_400 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1))
                                      (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3) (coe v4)
                                      (coe v11) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_400 (coe v0)
                                         (coe addInt (coe (3 :: Integer)) (coe v1))
                                         (coe addInt (coe (2 :: Integer)) (coe v2)) (coe v3)
                                         (coe v4) (coe v11) (coe v9))))
                                (coe v3) (coe v4) (coe v12) (coe v10))))
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                   (coe v1))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v2))))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                      (coe v1))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_resuspend'45'layer_400 (coe v0)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_resuspend'45'layer_400 (coe v0)
                                                  (coe addInt (coe (3 :: Integer)) (coe v1))
                                                  (coe addInt (coe (2 :: Integer)) (coe v2))
                                                  (coe v3) (coe v4) (coe v11) (coe v9)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_resuspend'45'layer_400 (coe v0)
                                                     (coe addInt (coe (3 :: Integer)) (coe v1))
                                                     (coe addInt (coe (2 :: Integer)) (coe v2))
                                                     (coe v3) (coe v4) (coe v11) (coe v9))))
                                            (coe v3) (coe v4) (coe v12) (coe v10))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                         (coe addInt (coe (2 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                            (coe (2 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                               (coe addInt (coe (1 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                     (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                           (coe (1 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                 (coe
                                                                    addInt (coe (1 :: Integer))
                                                                    (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                         (coe
                                            MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                               (coe v2))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_resuspend'45'layer_400 (coe v0)
                                                  (coe addInt (coe (3 :: Integer)) (coe v1))
                                                  (coe addInt (coe (2 :: Integer)) (coe v2))
                                                  (coe v3) (coe v4) (coe v11) (coe v9))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                               (coe addInt (coe (2 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                  (coe (2 :: Integer)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                           (coe
                                                              addInt (coe (2 :: Integer)) (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                                                 (coe (0 :: Integer)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v1)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v2)))))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IRTy.C_wf'45'Prod_140 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.IRTy.C__'8855'__14 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_resuspend'45'layer_400 (coe v0)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_resuspend'45'layer_400 (coe v0)
                                (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                (coe v4) (coe v11) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_resuspend'45'layer_400 (coe v0)
                                   (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                   (coe v4) (coe v11) (coe v9))))
                          (coe v3) (coe v4) (coe v12) (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_resuspend'45'layer_400 (coe v0)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_resuspend'45'layer_400 (coe v0)
                                      (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2) (coe v3)
                                      (coe v4) (coe v11) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_resuspend'45'layer_400 (coe v0)
                                         (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                         (coe v3) (coe v4) (coe v11) (coe v9))))
                                (coe v3) (coe v4) (coe v12) (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                             (coe v1))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                (coe v1))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_resuspend'45'layer_400 (coe v0)
                                            (coe addInt (coe (3 :: Integer)) (coe v1)) (coe v2)
                                            (coe v3) (coe v4) (coe v11) (coe v9))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                         (coe addInt (coe (2 :: Integer)) (coe v1)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                            (coe (2 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                               (coe addInt (coe (1 :: Integer)) (coe v1)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                     (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                    (coe
                                                                       d_resuspend'45'layer_400
                                                                       (coe v0)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe
                                                                             d_resuspend'45'layer_400
                                                                             (coe v0)
                                                                             (coe
                                                                                addInt
                                                                                (coe (3 :: Integer))
                                                                                (coe v1))
                                                                             (coe v2) (coe v3)
                                                                             (coe v4) (coe v11)
                                                                             (coe v9)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                             (coe
                                                                                d_resuspend'45'layer_400
                                                                                (coe v0)
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      (3 ::
                                                                                         Integer))
                                                                                   (coe v1))
                                                                                (coe v2) (coe v3)
                                                                                (coe v4) (coe v11)
                                                                                (coe v9))))
                                                                       (coe v3) (coe v4) (coe v12)
                                                                       (coe v10))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                                    (coe
                                                                       addInt (coe (2 :: Integer))
                                                                       (coe v1)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v1)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                          (coe
                                                                             addInt
                                                                             (coe (2 :: Integer))
                                                                             (coe v1)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      (1 ::
                                                                                         Integer))
                                                                                   (coe v1)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cmp-trace
d_cmp'45'trace_496 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_cmp'45'trace_496 ~v0 v1 v2 = du_cmp'45'trace_496 v1 v2
du_cmp'45'trace_496 ::
  MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_cmp'45'trace_496 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296
         (coe
            MAlonzo.Code.Once.Type.C__'42'__124
            (coe MAlonzo.Code.Once.Type.C_Int_134)
            (coe MAlonzo.Code.Once.Type.C_Int_134))
         (coe MAlonzo.Code.Once.Type.C_Int_134)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Compare.d_cmp'45'block'45'info_24
            (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2316
            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_out'45'nz_382))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
               (coe v1))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                  (coe (2 :: Integer)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                     (coe addInt (coe (1 :: Integer)) (coe v1)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                 (coe (0 :: Integer)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                       (coe addInt (coe (1 :: Integer)) (coe v1)))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.CCC.Codegen.IRToTrace.sigop-budget
d_sigop'45'budget_502 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
d_sigop'45'budget_502 ~v0 v1 v2 = du_sigop'45'budget_502 v1 v2
du_sigop'45'budget_502 ::
  Integer -> Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 -> Integer
du_sigop'45'budget_502 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (2 :: Integer)) (coe v0)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-code
d_sigop'45'code_512 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_sigop'45'code_512 ~v0 v1 v2 v3 v4 v5
  = du_sigop'45'code_512 v1 v2 v3 v4 v5
du_sigop'45'code_512 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_sigop'45'code_512 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe du_cmp'45'trace_496 (coe v5) (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2296 (coe v0)
                (coe v1) (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.sigop-trace
d_sigop'45'trace_528 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigop'45'trace_528 ~v0 v1 v2 v3 v4 v5 v6
  = du_sigop'45'trace_528 v1 v2 v3 v4 v5 v6
du_sigop'45'trace_528 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  Maybe MAlonzo.Code.Once.Arith.CmpOp.T_CmpOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigop'45'trace_528 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_sigop'45'budget_502 (coe v2) (coe v5))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               du_sigop'45'code_512 (coe v0) (coe v1) (coe v4) (coe v2) (coe v5))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace'
d_ir'45'to'45'trace''_542 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_542 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_ir'45'to'45'trace''_542 (coe v0) (coe v7) (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                         (coe v4) (coe v10)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                            (coe v4) (coe v10))))
                   (coe v9)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_ir'45'to'45'trace''_542 (coe v0) (coe v7) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                               (coe v4) (coe v10)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10))))
                         (coe v9))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_ir'45'to'45'trace''_542 (coe v0) (coe v7) (coe v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7)
                                           (coe v3) (coe v4) (coe v10)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7)
                                              (coe v3) (coe v4) (coe v10))))
                                     (coe v9)))))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7) (coe v3)
                                  (coe v4) (coe v10)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v7) (coe v2)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7)
                                        (coe v3) (coe v4) (coe v10)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v7)
                                           (coe v3) (coe v4) (coe v10))))
                                  (coe v9))))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v12)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                   (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v12)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                      (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9))))
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                   (coe v3))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2270
                                            (coe v3))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              d_ir'45'to'45'trace''_542 (coe v0)
                                                              (coe v1) (coe v11)
                                                              (coe
                                                                 addInt (coe (4 :: Integer))
                                                                 (coe v3))
                                                              (coe v4) (coe v9)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_ir'45'to'45'trace''_542 (coe v0)
                                                                 (coe v1) (coe v11)
                                                                 (coe
                                                                    addInt (coe (4 :: Integer))
                                                                    (coe v3))
                                                                 (coe v4) (coe v9))))
                                                        (coe v10)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                  (coe addInt (coe (2 :: Integer)) (coe v3)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                                     (coe (2 :: Integer)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                        (coe addInt (coe (3 :: Integer)) (coe v3)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe v3)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                    (coe
                                                                       addInt (coe (2 :: Integer))
                                                                       (coe v3)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                          (coe
                                                                             addInt
                                                                             (coe (3 :: Integer))
                                                                             (coe v3)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                         (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v12)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v11)
                                               (coe addInt (coe (4 :: Integer)) (coe v3)) (coe v4)
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                  (coe v11)
                                                  (coe addInt (coe (4 :: Integer)) (coe v3))
                                                  (coe v4) (coe v9))))
                                         (coe v10))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                        (coe (0 :: Integer)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                              (coe v3))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2308
                                        (coe (1 :: Integer)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                              (coe v3))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_542 (coe v0) (coe v12) (coe v2)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2) (coe v3)
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2) (coe v3)
                                   (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_542 (coe v0) (coe v12) (coe v2)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2) (coe v3)
                                      (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2)
                                         (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                         (coe v9))))
                                (coe v10))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234
                                      (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_ir'45'to'45'trace''_542 (coe v0) (coe v12) (coe v2)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_ir'45'to'45'trace''_542 (coe v0) (coe v11)
                                                     (coe v2) (coe v3)
                                                     (coe addInt (coe (2 :: Integer)) (coe v4))
                                                     (coe v9))))
                                            (coe v10)))))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230
                                            (coe
                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                  (coe v4))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9)))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                  (coe addInt (coe (1 :: Integer)) (coe v4)))))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2)
                                         (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                         (coe v9)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v12) (coe v2)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_542 (coe v0) (coe v11) (coe v2)
                                               (coe v3) (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_542 (coe v0) (coe v11)
                                                  (coe v2) (coe v3)
                                                  (coe addInt (coe (2 :: Integer)) (coe v4))
                                                  (coe v9))))
                                         (coe v10))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_542 (coe v0)
                                (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                (coe v11) (coe (0 :: Integer))
                                (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                   (coe v3))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                         (coe addInt (coe (1 :: Integer)) (coe v3)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                               (coe v3))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                        (coe v4)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v3)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                         (coe v11) (coe (0 :: Integer))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_542 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1)
                                                  (coe v10))
                                               (coe v11) (coe (0 :: Integer))
                                               (coe addInt (coe (2 :: Integer)) (coe v4))
                                               (coe v9)))))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_542 (coe v0)
                                         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10))
                                         (coe v11) (coe (0 :: Integer))
                                         (coe addInt (coe (2 :: Integer)) (coe v4)) (coe v9))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (3 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2258)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                           (coe addInt (coe (1 :: Integer)) (coe v3)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                              (coe (2 :: Integer)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                 (coe addInt (coe (2 :: Integer)) (coe v3)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                       (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                             (coe v3))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v3)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_cata'45'dispatch_362 (coe v0)
                                 (coe
                                    du_cata'45'strategy_50
                                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v13)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_542 (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v13)
                                             (coe v2)))
                                       (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_542 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                (coe v13) (coe v2)))
                                          (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ir'45'to'45'trace''_542 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_cata'45'dispatch_362 (coe v0)
                                       (coe
                                          du_cata'45'strategy_50
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608 (coe v13)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_542 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_542 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_542 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v2)))
                                                   (coe v2) (coe (0 :: Integer)) (coe v4)
                                                   (coe v10))))))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_cata'45'dispatch_362 (coe v0)
                                          (coe
                                             du_cata'45'strategy_50
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_608
                                                (coe v13)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_ir'45'to'45'trace''_542 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                      (coe v13) (coe v2)))
                                                (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))
                                          (coe v3)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_ir'45'to'45'trace''_542 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v2)))
                                                   (coe v2) (coe (0 :: Integer)) (coe v4)
                                                   (coe v10))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_542 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                            (coe v13) (coe v2)))
                                                      (coe v2) (coe (0 :: Integer)) (coe v4)
                                                      (coe v10))))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ir'45'to'45'trace''_542 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v2)))
                                             (coe v2) (coe (0 :: Integer)) (coe v4) (coe v10)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2306)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2256)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2282)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (2 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe addInt (coe (1 :: Integer)) (coe v4))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                            (coe v3))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                  (coe addInt (coe (1 :: Integer)) (coe v3)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                        (coe v3))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                 (coe v4)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                    (coe addInt (coe (1 :: Integer)) (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (2 :: Integer)) (coe v3))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_resuspend'45'layer_400 (coe v0)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                (coe v13) (coe v12))
                                             (coe (1 :: Integer))
                                             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v10)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))
                                       (coe (0 :: Integer)) (coe v13) (coe v7))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                          (coe v3))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2312
                                             (coe (2 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2254)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                      (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2264)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2304
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                               (coe v0) (coe v4)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2266)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2260
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v3)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0) (coe v4))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_resuspend'45'layer_400 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                         (coe v13) (coe v12))
                                                      (coe (1 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v4))
                                                      (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                            (coe v13) (coe v12))
                                                         (coe (1 :: Integer))
                                                         (coe addInt (coe (1 :: Integer)) (coe v4))
                                                         (coe v10))))
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Label.d_ℓ_408 (coe v0)
                                                   (coe v4))
                                                (coe (0 :: Integer)) (coe v13) (coe v7)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2252)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2262
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               d_ir'45'to'45'trace''_542 (coe v0)
                                                               (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                  (coe v13) (coe v12))
                                                               (coe (1 :: Integer))
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v4))
                                                               (coe v10)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            d_resuspend'45'layer_400 (coe v0)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  d_ir'45'to'45'trace''_542 (coe v0)
                                                                  (coe v1)
                                                                  (coe
                                                                     MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                     (coe v13) (coe v12))
                                                                  (coe (1 :: Integer))
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v4))
                                                                  (coe v10)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_542
                                                                     (coe v0) (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                                        (coe v13) (coe v12))
                                                                     (coe (1 :: Integer))
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v4))
                                                                     (coe v10))))
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Label.d_ℓ_408
                                                               (coe v0) (coe v4))
                                                            (coe (0 :: Integer)) (coe v13)
                                                            (coe v7)))))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_542 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80
                                                   (coe v13) (coe v12))
                                                (coe (1 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v4))
                                                (coe v10))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_126 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_520
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'int_202) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_522
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2302
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'float_204) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_132 v6 v7 v8
        -> coe
             du_sigop'45'trace_528 (coe v6) (coe v7) (coe v3) (coe v4) (coe v8)
             (coe
                MAlonzo.Code.Once.Arith.SigOp.Compare.du_cmp'45'of_12
                (coe MAlonzo.Code.Once.SigOp.Info.d_sem_180 (coe v8)))
      MAlonzo.Code.Once.IR.C_Call_138 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240
                            (coe v8)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-trace
d_proj'45'trace_822 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_proj'45'trace_822 ~v0 v1 = du_proj'45'trace_822 v1
du_proj'45'trace_822 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
du_proj'45'trace_822 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-bodies
d_proj'45'bodies_826 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_proj'45'bodies_826 ~v0 v1 = du_proj'45'bodies_826 v1
du_proj'45'bodies_826 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_proj'45'bodies_826 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6 -> coe v6
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-budget
d_proj'45'budget_830 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'budget_830 ~v0 v1 = du_proj'45'budget_830 v1
du_proj'45'budget_830 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'budget_830 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-label
d_proj'45'label_834 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'label_834 ~v0 v1 = du_proj'45'label_834 v1
du_proj'45'label_834 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
du_proj'45'label_834 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-unit-at
d_ir'45'to'45'unit'45'at_842 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2326
d_ir'45'to'45'unit'45'at_842 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_unit_2340
      (coe
         du_proj'45'budget_830
         (coe
            d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'trace_822
         (coe
            d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
      (coe
         du_proj'45'bodies_826
         (coe
            d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe v4) (coe v5)))
-- Once.CCC.Codegen.IRToTrace.ir-to-unit
d_ir'45'to'45'unit_854 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_CompUnit_2326
d_ir'45'to'45'unit_854 v0 v1 v2
  = coe
      d_ir'45'to'45'unit'45'at_842 (coe v0) (coe v1) (coe v2)
      (coe (0 :: Integer)) (coe (0 :: Integer))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace
d_ir'45'to'45'trace_860 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace_860 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2372
      (coe d_ir'45'to'45'unit_854 v0 v1 v2 v3)
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_868 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace'45'at'45'frontier_868 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2372
      (coe
         d_ir'45'to'45'unit'45'at_842 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe (0 :: Integer)) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget
d_ir'45'stack'45'budget_878 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_878 v0 v1 v2 v3
  = coe
      du_proj'45'budget_830
      (coe
         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies
d_ir'45'to'45'bodies_886 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ir'45'to'45'bodies_886 v0 v1 v2 v3
  = coe
      du_proj'45'bodies_826
      (coe
         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-from
d_ir'45'to'45'trace'45'from_894 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace'45'from_894 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_908 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_908 v0 v1 v2 v3 v4
  = coe
      du_proj'45'budget_830
      (coe
         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-linked-from
d_ir'45'to'45'linked'45'from_918 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'linked'45'from_918 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2372
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_unit_2340
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
                        (coe (0 :: Integer)) (coe v3) (coe v4)))))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                     (coe
                        d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
                        (coe (0 :: Integer)) (coe v3) (coe v4)))))))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-lab
d_ir'45'to'45'trace'45'lab_936 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_ir'45'to'45'trace'45'lab_936 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.CCC.Machine.SMCore.d_link_2372
      (coe
         d_ir'45'to'45'unit'45'at_842 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-next-label
d_ir'45'next'45'label_946 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'next'45'label_946 v0 v1 v2 v3 v4
  = coe
      du_proj'45'label_834
      (coe
         d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3) (coe v4))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies-from
d_ir'45'to'45'bodies'45'from_956 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'bodies'45'from_956 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
               (coe (0 :: Integer)) (coe v3) (coe v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_542 (coe v0) (coe v1) (coe v2)
                  (coe (0 :: Integer)) (coe v3) (coe v4)))))
