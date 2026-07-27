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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRToTrace.rec-count
d_rec'45'count_8 :: MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
d_rec'45'count_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Once.Type.C_Id_116 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C__'8853'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe d_rec'45'count_8 (coe v1)) (coe d_rec'45'count_8 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__120 v1 v2
        -> coe
             addInt (coe d_rec'45'count_8 (coe v1))
             (coe d_rec'45'count_8 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.CataStrategy
d_CataStrategy_18 = ()
data T_CataStrategy_18
  = C_strat'45'const_20 | C_strat'45'nat_22 | C_strat'45'linear_24 |
    C_strat'45'branching_26 MAlonzo.Code.Once.Type.T_Functor_110
-- Once.CCC.Codegen.IRToTrace.has-id
d_has'45'id_28 :: MAlonzo.Code.Once.Type.T_Functor_110 -> Bool
d_has'45'id_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Once.Type.C__'8853'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'id_28 (coe v1)) (coe d_has'45'id_28 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__120 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'id_28 (coe v1)) (coe d_has'45'id_28 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.id-under-product
d_id'45'under'45'product_38 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> Bool
d_id'45'under'45'product_38 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Type.C__'8853'__118 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_id'45'under'45'product_38 (coe v1))
             (coe d_id'45'under'45'product_38 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__120 v1 v2
        -> coe
             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
             (coe d_has'45'id_28 (coe v1))
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe d_has'45'id_28 (coe v2))
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe d_id'45'under'45'product_38 (coe v1))
                   (coe d_id'45'under'45'product_38 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-strategy
d_cata'45'strategy_48 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> T_CataStrategy_18
d_cata'45'strategy_48 v0
  = let v1 = d_rec'45'count_8 (coe v0) in
    coe
      (case coe v1 of
         0 -> coe C_strat'45'const_20
         1 -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe d_id'45'under'45'product_38 (coe v0))
                (coe C_strat'45'linear_24) (coe C_strat'45'nat_22)
         _ -> coe C_strat'45'branching_26 (coe v0))
-- Once.CCC.Codegen.IRToTrace.cata-trace-nat
d_cata'45'trace'45'nat_62 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'nat_62 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (2 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (6 :: Integer)) (coe v1))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
               (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_424))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068 (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2072
                              (coe addInt (coe (1 :: Integer)) (coe v1))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074
                                 (coe addInt (coe (2 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                             (coe addInt (coe (3 :: Integer)) (coe v1))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                (coe addInt (coe (2 :: Integer)) (coe v1))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_426))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                      (coe addInt (coe (3 :: Integer)) (coe v1))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                                         (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v1))))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                           (coe (0 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                       (coe v0))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                          (coe (2 :: Integer)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                             (coe addInt (coe (1 :: Integer)) (coe v0)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                                   (coe (0 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                         (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                               (coe
                                                                  addInt (coe (1 :: Integer))
                                                                  (coe v0)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                             (coe addInt (coe (4 :: Integer)) (coe v1))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2072
                                                (coe addInt (coe (5 :: Integer)) (coe v1))))
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                            (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                                               (coe (2 :: Integer)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v0)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                                                        (coe (1 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                              (coe v0))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v0)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                         (coe v2)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                                      (coe addInt (coe (4 :: Integer)) (coe v1))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                         (coe
                                                            addInt (coe (5 :: Integer)) (coe v1))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))
-- Once.CCC.Codegen.IRToTrace.cata-trace-linear
d_cata'45'trace'45'linear_102 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'linear_102 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe addInt (coe (6 :: Integer)) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (4 :: Integer)) (coe v1))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_432))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                     (coe (0 :: Integer)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                        (coe addInt (coe (3 :: Integer)) (coe v0)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068 (coe v1)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074
                                 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                                 (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_434))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                             (coe addInt (coe (5 :: Integer)) (coe v0)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                   (coe addInt (coe (2 :: Integer)) (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                                      (coe (2 :: Integer)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                         (coe addInt (coe (1 :: Integer)) (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                               (coe
                                                                  addInt (coe (5 :: Integer))
                                                                  (coe v0)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v0)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v0)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                                              (coe
                                                                                 addInt
                                                                                 (coe
                                                                                    (3 :: Integer))
                                                                                 (coe v0)))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (2 ::
                                                                                          Integer))
                                                                                    (coe v0)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                                                                          (coe v1)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v1))))
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_430))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                           (coe addInt (coe (2 :: Integer)) (coe v1))))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2072
                              (coe addInt (coe (3 :: Integer)) (coe v1))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                              (coe addInt (coe (4 :: Integer)) (coe v0)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                 (coe addInt (coe (3 :: Integer)) (coe v0)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe addInt (coe (5 :: Integer)) (coe v0)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (3 :: Integer)) (coe v0)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                                   (coe (2 :: Integer)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                      (coe addInt (coe (1 :: Integer)) (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                            (coe
                                                               addInt (coe (5 :: Integer))
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                  (coe
                                                                     addInt (coe (4 :: Integer))
                                                                     (coe v0)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                                                        (coe (2 :: Integer)))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                                           (coe v0))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                                                                 (coe
                                                                                    (1 :: Integer)))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                                       (coe
                                                                                          addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe v0)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                                             (coe
                                                                                                v0))
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2144
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_428))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                                                                                            (coe
                                                                                                               addInt
                                                                                                               (coe
                                                                                                                  (2 ::
                                                                                                                     Integer))
                                                                                                               (coe
                                                                                                                  v1))))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                                                                                               (coe
                                                                                                                  addInt
                                                                                                                  (coe
                                                                                                                     (3 ::
                                                                                                                        Integer))
                                                                                                                  (coe
                                                                                                                     v1))))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))))))))))
-- Once.CCC.Codegen.IRToTrace.fsize
d_fsize_140 :: MAlonzo.Code.Once.Type.T_Functor_110 -> Integer
d_fsize_140 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C_Id_116 -> coe (1 :: Integer)
      MAlonzo.Code.Once.Type.C__'8853'__118 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe d_fsize_140 (coe v1)))
             (coe d_fsize_140 (coe v2))
      MAlonzo.Code.Once.Type.C__'8855'__120 v1 v2
        -> coe
             addInt (coe addInt (coe (1 :: Integer)) (coe d_fsize_140 (coe v1)))
             (coe d_fsize_140 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.push2
d_push2_156 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_push2_156 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
               (coe v2))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                     (coe v1))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                           (coe v0))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                    (coe v0))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))
-- Once.CCC.Codegen.IRToTrace.pop2
d_pop2_166 ::
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_pop2_166 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
         (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                  (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Once.CCC.Codegen.IRToTrace.wrap-sum
d_wrap'45'sum_174 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_wrap'45'sum_174 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
            (coe (2 :: Integer)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
               (coe addInt (coe (1 :: Integer)) (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                     (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                 (coe addInt (coe (1 :: Integer)) (coe v1)))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Once.CCC.Codegen.IRToTrace.visit-walk
d_visit'45'walk_188 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_visit'45'walk_188 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_K_114 v5
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Type.C_Id_116
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
             (coe d_push2_156 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Once.Type.C__'8853'__118 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      d_visit'45'walk_188 (coe v0) (coe v1) (coe v2) (coe v5)
                      (coe addInt (coe (4 :: Integer)) (coe v4))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      d_visit'45'walk_188 (coe v0) (coe v1) (coe v2) (coe v6)
                      (coe addInt (coe (4 :: Integer)) (coe v4)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C__'8855'__120 v5 v6
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                      (coe v4))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_visit'45'walk_188 (coe v0) (coe v1) (coe v2) (coe v6)
                   (coe addInt (coe (4 :: Integer)) (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100
                         (coe v4))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   (coe
                      d_visit'45'walk_188 (coe v0) (coe v1) (coe v2) (coe v5)
                      (coe addInt (coe (4 :: Integer)) (coe v4)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.rebuild-walk
d_rebuild'45'walk_238 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_rebuild'45'walk_238 v0 ~v1 ~v2 v3 v4
  = du_rebuild'45'walk_238 v0 v3 v4
du_rebuild'45'walk_238 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
du_rebuild'45'walk_238 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_K_114 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_Id_116 -> coe d_pop2_166 (coe v0)
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_238 (coe v0) (coe v3)
                         (coe addInt (coe (4 :: Integer)) (coe v2)))
                      (coe d_wrap'45'sum_174 (coe (0 :: Integer)) (coe v2))))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_238 (coe v0) (coe v4)
                         (coe addInt (coe (4 :: Integer)) (coe v2)))
                      (coe d_wrap'45'sum_174 (coe (1 :: Integer)) (coe v2)))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                      (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   du_rebuild'45'walk_238 (coe v0) (coe v3)
                   (coe addInt (coe (4 :: Integer)) (coe v2)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100
                            (coe v2))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         du_rebuild'45'walk_238 (coe v0) (coe v4)
                         (coe addInt (coe (4 :: Integer)) (coe v2)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                            (coe addInt (coe (2 :: Integer)) (coe v2)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe
                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                               (coe (2 :: Integer)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                  (coe addInt (coe (3 :: Integer)) (coe v2)))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                        (coe addInt (coe (1 :: Integer)) (coe v2)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                              (coe addInt (coe (2 :: Integer)) (coe v2)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                    (coe addInt (coe (3 :: Integer)) (coe v2)))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.cata-trace-branching
d_cata'45'trace'45'branching_280 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'trace'45'branching_280 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt
         (coe
            addInt (coe (11 :: Integer))
            (coe mulInt (coe (4 :: Integer)) (coe d_fsize_140 (coe v0))))
         (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (4 :: Integer)) (coe v2))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                        (coe addInt (coe (3 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                           (coe (2 :: Integer)))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                              (coe addInt (coe (6 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                    (coe (0 :: Integer)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                          (coe addInt (coe (6 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                             (coe addInt (coe (1 :: Integer)) (coe v1)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                (coe addInt (coe (6 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                   (coe addInt (coe (2 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                      (coe addInt (coe (6 :: Integer)) (coe v1)))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                         (coe v1))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                            (coe
                                                               addInt (coe (3 :: Integer))
                                                               (coe v1)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
               (coe
                  d_push2_156 (coe v1) (coe addInt (coe (4 :: Integer)) (coe v1))
                  (coe addInt (coe (5 :: Integer)) (coe v1))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068 (coe v2)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                           (coe v1))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074
                                    (coe addInt (coe (1 :: Integer)) (coe v2))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (3 :: Integer)) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                   (coe addInt (coe (3 :: Integer)) (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        d_push2_156 (coe addInt (coe (1 :: Integer)) (coe v1))
                        (coe addInt (coe (4 :: Integer)) (coe v1))
                        (coe addInt (coe (5 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                              (coe addInt (coe (3 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_visit'45'walk_188 (coe v1)
                              (coe addInt (coe (4 :: Integer)) (coe v1))
                              (coe addInt (coe (5 :: Integer)) (coe v1)) (coe v0)
                              (coe addInt (coe (7 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070 (coe v2)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                       (coe addInt (coe (1 :: Integer)) (coe v2))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                              (coe addInt (coe (2 :: Integer)) (coe v2))))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                              (coe addInt (coe (1 :: Integer)) (coe v1)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2074
                                       (coe addInt (coe (3 :: Integer)) (coe v2))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe addInt (coe (1 :: Integer)) (coe v1)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe
                           du_rebuild'45'walk_238 (coe addInt (coe (2 :: Integer)) (coe v1))
                           (coe v0) (coe addInt (coe (7 :: Integer)) (coe v1)))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe
                                    d_push2_156 (coe addInt (coe (2 :: Integer)) (coe v1))
                                    (coe addInt (coe (4 :: Integer)) (coe v1))
                                    (coe addInt (coe (5 :: Integer)) (coe v1)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2070
                                          (coe addInt (coe (2 :: Integer)) (coe v2))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2146
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2068
                                             (coe addInt (coe (3 :: Integer)) (coe v2))))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                        (coe addInt (coe (2 :: Integer)) (coe v1)))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CCC.Codegen.IRToTrace.cata-dispatch
d_cata'45'dispatch_326 ::
  T_CataStrategy_18 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'dispatch_326 v0 v1 v2 v3
  = case coe v0 of
      C_strat'45'const_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
      C_strat'45'nat_22
        -> coe d_cata'45'trace'45'nat_62 (coe v1) (coe v2) (coe v3)
      C_strat'45'linear_24
        -> coe d_cata'45'trace'45'linear_102 (coe v1) (coe v2) (coe v3)
      C_strat'45'branching_26 v4
        -> coe
             d_cata'45'trace'45'branching_280 (coe v4) (coe v1) (coe v2)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-trace'
d_ir'45'to'45'trace''_358 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_358 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C__'8728'__30 v6 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_ir'45'to'45'trace''_358 (coe v6) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                         (coe v9)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                            (coe v9))))
                   (coe v8)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_ir'45'to'45'trace''_358 (coe v6) (coe v1)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                               (coe v9)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                                  (coe v9))))
                         (coe v8))))
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
                                  d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                                  (coe v9)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_ir'45'to'45'trace''_358 (coe v6) (coe v1)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2)
                                           (coe v3) (coe v9)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2)
                                              (coe v3) (coe v9))))
                                     (coe v8)))))))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2) (coe v3)
                                  (coe v9)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_358 (coe v6) (coe v1)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2)
                                        (coe v3) (coe v9)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_ir'45'to'45'trace''_358 (coe v0) (coe v6) (coe v2)
                                           (coe v3) (coe v9))))
                                  (coe v8))))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                       (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                       (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                          (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                          (coe v8))))
                                 (coe v9)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                             (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8))))
                                       (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                      (coe addInt (coe (3 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               d_ir'45'to'45'trace''_358 (coe v0)
                                                               (coe v12)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_358
                                                                     (coe v0) (coe v11)
                                                                     (coe
                                                                        addInt (coe (3 :: Integer))
                                                                        (coe v2))
                                                                     (coe v3) (coe v8)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        d_ir'45'to'45'trace''_358
                                                                        (coe v0) (coe v11)
                                                                        (coe
                                                                           addInt
                                                                           (coe (3 :: Integer))
                                                                           (coe v2))
                                                                        (coe v3) (coe v8))))
                                                               (coe v9)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                         (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe v2)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                      (coe addInt (coe (3 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_358 (coe v0)
                                                         (coe v11)
                                                         (coe addInt (coe (3 :: Integer)) (coe v2))
                                                         (coe v3) (coe v8))))
                                                (coe v9))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                       (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                       (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                          (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                          (coe v8))))
                                 (coe v9)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                             (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8))))
                                       (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                      (coe addInt (coe (4 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2100
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               d_ir'45'to'45'trace''_358 (coe v0)
                                                               (coe v12)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_358
                                                                     (coe v0) (coe v11)
                                                                     (coe
                                                                        addInt (coe (4 :: Integer))
                                                                        (coe v2))
                                                                     (coe v3) (coe v8)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        d_ir'45'to'45'trace''_358
                                                                        (coe v0) (coe v11)
                                                                        (coe
                                                                           addInt
                                                                           (coe (4 :: Integer))
                                                                           (coe v2))
                                                                        (coe v3) (coe v8))))
                                                               (coe v9)))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                         (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                                            (coe (2 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                           (coe
                                                                              addInt
                                                                              (coe (2 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                                 (coe
                                                                                    addInt
                                                                                    (coe
                                                                                       (3 ::
                                                                                          Integer))
                                                                                    (coe v2)))
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
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358 (coe v0) (coe v12)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_358 (coe v0) (coe v11)
                                                      (coe addInt (coe (4 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_358 (coe v0)
                                                         (coe v11)
                                                         (coe addInt (coe (4 :: Integer)) (coe v2))
                                                         (coe v3) (coe v8))))
                                                (coe v9))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_44
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_snd_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_inl_56 v7
        -> case coe v7 of
             MAlonzo.Code.Once.IR.C_Stack_6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098
                                            (coe v2))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IR.C_Heap_8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                               (coe (0 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inr_62 v7
        -> case coe v7 of
             MAlonzo.Code.Once.IR.C_Stack_6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098
                                            (coe v2))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IR.C_Heap_8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe addInt (coe (2 :: Integer)) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2136
                                               (coe (1 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_case_70 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_358 (coe v11) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2) (coe v3)
                                (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2) (coe v3)
                                   (coe v8))))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_358 (coe v11) (coe v1)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2) (coe v3)
                                      (coe v8)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2)
                                         (coe v3) (coe v8))))
                                (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2138
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_358 (coe v10) (coe v1)
                                                  (coe v2) (coe v3) (coe v8)))))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_358 (coe v11) (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        d_ir'45'to'45'trace''_358 (coe v10) (coe v1)
                                                        (coe v2) (coe v3) (coe v8)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_ir'45'to'45'trace''_358 (coe v10)
                                                           (coe v1) (coe v2) (coe v3) (coe v8))))
                                                  (coe v9))))))))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2)
                                         (coe v3) (coe v8)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_358 (coe v11) (coe v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_358 (coe v10) (coe v1) (coe v2)
                                               (coe v3) (coe v8)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_358 (coe v10) (coe v1)
                                                  (coe v2) (coe v3) (coe v8))))
                                         (coe v9))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_74
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_initial_78
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_curry_86 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Once.IR.C_Stack_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (2 :: Integer)) (coe v2))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ir'45'to'45'trace''_358
                                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                       (coe v11) (coe (0 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v8))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2132
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2098
                                                   (coe v2))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_ir'45'to'45'trace''_358
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                   (coe v10))
                                                (coe v11) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_358
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                         (coe v10))
                                                      (coe v11) (coe (0 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v3))
                                                      (coe v8)))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                   (coe v10))
                                                (coe v11) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v8))))))))
                    MAlonzo.Code.Once.IR.C_Heap_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe addInt (coe (2 :: Integer)) (coe v2))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ir'45'to'45'trace''_358
                                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v10))
                                       (coe v11) (coe (0 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v8))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                             (coe (2 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2132
                                                            (coe v3))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe v2)))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                d_ir'45'to'45'trace''_358
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                   (coe v10))
                                                (coe v11) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v8)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_358
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                         (coe v10))
                                                      (coe v11) (coe (0 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v3))
                                                      (coe v8)))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_358
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0)
                                                   (coe v10))
                                                (coe v11) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v8))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_92
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe addInt (coe (3 :: Integer)) (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2088)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                            (coe v2))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2134)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2086)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                           (coe addInt (coe (1 :: Integer)) (coe v2)))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2140
                                              (coe (2 :: Integer)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2092
                                                 (coe addInt (coe (2 :: Integer)) (coe v2)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe
                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                       (coe addInt (coe (1 :: Integer)) (coe v2)))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe
                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2094)
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe
                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                             (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe
                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2096)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2090
                                                                   (coe
                                                                      addInt (coe (2 :: Integer))
                                                                      (coe v2)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2080)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2112)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_In_96 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_out'45'μ_100 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_cata'45'dispatch_326
                          (coe
                             d_cata'45'strategy_48
                             (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_358
                                (coe
                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9) (coe v1))
                                (coe v1) (coe v2) (coe v3) (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_358
                                   (coe
                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                      (coe v1))
                                   (coe v1) (coe v2) (coe v3) (coe v8))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_ir'45'to'45'trace''_358
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v3) (coe v8)))))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_cata'45'dispatch_326
                                (coe
                                   d_cata'45'strategy_48
                                   (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_358
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v3) (coe v8)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_358
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                            (coe v1))
                                         (coe v1) (coe v2) (coe v3) (coe v8))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_ir'45'to'45'trace''_358
                                            (coe
                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                               (coe v9) (coe v1))
                                            (coe v1) (coe v2) (coe v3) (coe v8))))))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_cata'45'dispatch_326
                                   (coe
                                      d_cata'45'strategy_48
                                      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_568 (coe v9)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_ir'45'to'45'trace''_358
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                            (coe v1))
                                         (coe v1) (coe v2) (coe v3) (coe v8)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_ir'45'to'45'trace''_358
                                            (coe
                                               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                               (coe v9) (coe v1))
                                            (coe v1) (coe v2) (coe v3) (coe v8))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               d_ir'45'to'45'trace''_358
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                  (coe v9) (coe v1))
                                               (coe v1) (coe v2) (coe v3) (coe v8))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_ir'45'to'45'trace''_358
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v9)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v3) (coe v8)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Para_112 v6 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Out_116 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_in'45'ν_120 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Hylo_134 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_Fuse_142 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_free'45'heap_144 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2078)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.IR.C_const_148 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_512
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2130
                                (coe MAlonzo.Code.Once.Type.C_Int_136)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'int_198) (coe v7))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_514
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2130
                                (coe MAlonzo.Code.Once.Type.C_Float_138)
                                (coe MAlonzo.Code.Once.Type.C_fits'45'float_200) (coe v7))
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_154 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2126 (coe v5)
                         (coe v6) (coe v7))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-trace
d_proj'45'trace_674 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_proj'45'trace_674 v0
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
d_proj'45'bodies_678 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_proj'45'bodies_678 v0
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
d_proj'45'budget_682 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'budget_682 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-trace
d_ir'45'to'45'trace_690 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_ir'45'to'45'trace_690 v0 v1 v2
  = coe
      d_proj'45'trace_674
      (coe
         d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_698 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2076]
d_ir'45'to'45'trace'45'at'45'frontier_698 v0 v1 v2 v3
  = coe
      d_proj'45'trace_674
      (coe
         d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget
d_ir'45'stack'45'budget_708 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget_708 v0 v1 v2
  = coe
      d_proj'45'budget_682
      (coe
         d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies
d_ir'45'to'45'bodies_716 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ir'45'to'45'bodies_716 v0 v1 v2
  = coe
      d_proj'45'bodies_678
      (coe
         d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-from
d_ir'45'to'45'trace'45'from_724 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace'45'from_724 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
               (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
                  (coe v2) (coe v3)))))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_738 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> Integer
d_ir'45'stack'45'budget'45'from_738 v0 v1 v2 v3
  = coe
      d_proj'45'budget_682
      (coe
         d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies-from
d_ir'45'to'45'bodies'45'from_748 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'bodies'45'from_748 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
               (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_358 (coe v0) (coe v1) (coe (0 :: Integer))
                  (coe v2) (coe v3)))))
