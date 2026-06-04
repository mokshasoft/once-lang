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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Codegen.IRToTrace.ir-to-trace'
d_ir'45'to'45'trace''_12 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace''_12 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.CCC.IR.C_id_278
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v6 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_ir'45'to'45'trace''_12 (coe v6) (coe v1)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                         (coe v9)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                            (coe v9))))
                   (coe v8)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         d_ir'45'to'45'trace''_12 (coe v6) (coe v1)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                               (coe v9)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
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
                                  d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                                  (coe v9)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_ir'45'to'45'trace''_12 (coe v6) (coe v1)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2)
                                           (coe v3) (coe v9)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2)
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
                                  d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                                  (coe v9)))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_ir'45'to'45'trace''_12 (coe v6) (coe v1)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2) (coe v3)
                                        (coe v9)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_ir'45'to'45'trace''_12 (coe v0) (coe v6) (coe v2)
                                           (coe v3) (coe v9))))
                                  (coe v8))))))))
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Once.CCC.IR.C_Stack_260
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                       (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                       (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
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
                                       d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                             (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8))))
                                       (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
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
                                                      d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                      (coe addInt (coe (3 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2058
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
                                                               d_ir'45'to'45'trace''_12 (coe v0)
                                                               (coe v12)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_12
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
                                                                        d_ir'45'to'45'trace''_12
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
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                         (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2056
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
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                (coe addInt (coe (3 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                      (coe addInt (coe (3 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                         (coe addInt (coe (3 :: Integer)) (coe v2))
                                                         (coe v3) (coe v8))))
                                                (coe v9))))))))
                    MAlonzo.Code.Once.CCC.IR.C_Heap_262
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                       (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                       (coe v8)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
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
                                       d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                             (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                             (coe v8)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8))))
                                       (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
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
                                                      d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                      (coe addInt (coe (4 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_restore'45'input_2058
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
                                                               d_ir'45'to'45'trace''_12 (coe v0)
                                                               (coe v12)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     d_ir'45'to'45'trace''_12
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
                                                                        d_ir'45'to'45'trace''_12
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
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                         (coe addInt (coe (2 :: Integer)) (coe v2)))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                                            (coe (2 :: Integer)))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                               (coe
                                                                  addInt (coe (3 :: Integer))
                                                                  (coe v2)))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                     (coe
                                                                        addInt (coe (1 :: Integer))
                                                                        (coe v2)))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                           (coe
                                                                              addInt
                                                                              (coe (2 :: Integer))
                                                                              (coe v2)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
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
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                (coe addInt (coe (4 :: Integer)) (coe v2)) (coe v3)
                                                (coe v8)))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12 (coe v0) (coe v12)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                      (coe addInt (coe (4 :: Integer)) (coe v2))
                                                      (coe v3) (coe v8)))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_ir'45'to'45'trace''_12 (coe v0) (coe v11)
                                                         (coe addInt (coe (4 :: Integer)) (coe v2))
                                                         (coe v3) (coe v8))))
                                                (coe v9))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_fst_300
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2044)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_snd_306
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2046)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_inl_312 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_260
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
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                (coe (0 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2056
                                            (coe v2))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.IR.C_Heap_262
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
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                               (coe (0 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_inr_318 v7
        -> case coe v7 of
             MAlonzo.Code.Once.CCC.IR.C_Stack_260
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
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                (coe (1 :: Integer)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2056
                                            (coe v2))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             MAlonzo.Code.Once.CCC.IR.C_Heap_262
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
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                      (coe (2 :: Integer)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                         (coe addInt (coe (1 :: Integer)) (coe v2)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                               (coe (1 :: Integer)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                           (coe
                                                              addInt (coe (1 :: Integer)) (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_case_326 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          d_ir'45'to'45'trace''_12 (coe v11) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2) (coe v3)
                                (coe v8)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2) (coe v3)
                                   (coe v8))))
                          (coe v9)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_ir'45'to'45'trace''_12 (coe v11) (coe v1)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2) (coe v3)
                                      (coe v8)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2)
                                         (coe v3) (coe v8))))
                                (coe v9))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'case'45'on'45'tag_2096
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2046)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_12 (coe v10) (coe v1)
                                                  (coe v2) (coe v3) (coe v8)))))))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2046)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_12 (coe v11) (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        d_ir'45'to'45'trace''_12 (coe v10) (coe v1)
                                                        (coe v2) (coe v3) (coe v8)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_ir'45'to'45'trace''_12 (coe v10)
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
                                         d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2)
                                         (coe v3) (coe v8)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                      (coe
                                         d_ir'45'to'45'trace''_12 (coe v11) (coe v1)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               d_ir'45'to'45'trace''_12 (coe v10) (coe v1) (coe v2)
                                               (coe v3) (coe v8)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_ir'45'to'45'trace''_12 (coe v10) (coe v1)
                                                  (coe v2) (coe v3) (coe v8))))
                                         (coe v9))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_terminal_330
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_initial_334
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_curry_344 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> case coe v10 of
                    MAlonzo.Code.Once.CCC.IR.C_Stack_260
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
                                       d_ir'45'to'45'trace''_12
                                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v11))
                                       (coe v13) (coe (0 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2090
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2056
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
                                                d_ir'45'to'45'trace''_12
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__122 (coe v0)
                                                   (coe v11))
                                                (coe v13) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_12
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'42'__122
                                                         (coe v0) (coe v11))
                                                      (coe v13) (coe (0 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v3))
                                                      (coe v9)))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__122 (coe v0)
                                                   (coe v11))
                                                (coe v13) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v9))))))))
                    MAlonzo.Code.Once.CCC.IR.C_Heap_262
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
                                       d_ir'45'to'45'trace''_12
                                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v11))
                                       (coe v13) (coe (0 :: Integer))
                                       (coe addInt (coe (1 :: Integer)) (coe v3)) (coe v9))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                          (coe v2))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe
                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                             (coe (2 :: Integer)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe
                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                (coe addInt (coe (1 :: Integer)) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe
                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                      (coe v2))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'code'45'addr_2090
                                                            (coe v3))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
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
                                                d_ir'45'to'45'trace''_12
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__122 (coe v0)
                                                   (coe v11))
                                                (coe v13) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v9)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_ir'45'to'45'trace''_12
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'42'__122
                                                         (coe v0) (coe v11))
                                                      (coe v13) (coe (0 :: Integer))
                                                      (coe addInt (coe (1 :: Integer)) (coe v3))
                                                      (coe v9)))))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                             (coe
                                                d_ir'45'to'45'trace''_12
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__122 (coe v0)
                                                   (coe v11))
                                                (coe v13) (coe (0 :: Integer))
                                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                                (coe v9))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_apply_352
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
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2046)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                            (coe addInt (coe (1 :: Integer)) (coe v2)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2044)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'save'45'closure'45'reg_2092)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect_2044)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                           (coe v2))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_lea'45'slot_2056
                                              (coe v2))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe
                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'call'45'closure_2070)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_arr_360
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_In_364 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_out'45'μ_368 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_Cata_374 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       addInt (coe (2 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_ir'45'to'45'trace''_12
                             (coe
                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v9) (coe v1))
                             (coe v1) (coe v2) (coe v3) (coe v8))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          addInt (coe (6 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   d_ir'45'to'45'trace''_12
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v9)
                                      (coe v1))
                                   (coe v1) (coe v2) (coe v3) (coe v8)))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'one_436))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                   (coe MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'zero_444))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     d_ir'45'to'45'trace''_12
                                                     (coe
                                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                        (coe v9) (coe v1))
                                                     (coe v1) (coe v2) (coe v3) (coe v8))))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2030
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_ir'45'to'45'trace''_12
                                                           (coe
                                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                              (coe v9) (coe v1))
                                                           (coe v1) (coe v2) (coe v3) (coe v8)))))))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2032
                                                  (coe
                                                     addInt (coe (2 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              d_ir'45'to'45'trace''_12
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v9) (coe v1))
                                                              (coe v1) (coe v2) (coe v3)
                                                              (coe v8)))))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_input2'45'inc_446))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'indirect'45'suc_2046)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2028
                                                              (coe
                                                                 addInt (coe (3 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                       (coe
                                                                          d_ir'45'to'45'trace''_12
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                             (coe v9) (coe v1))
                                                                          (coe v1) (coe v2) (coe v3)
                                                                          (coe v8)))))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                                                 (coe
                                                                    addInt (coe (2 :: Integer))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                          (coe
                                                                             d_ir'45'to'45'trace''_12
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v9) (coe v1))
                                                                             (coe v1) (coe v2)
                                                                             (coe v3) (coe v8)))))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'zero_438))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                                                       (coe
                                                                          addInt
                                                                          (coe (3 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   d_ir'45'to'45'trace''_12
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                      (coe v9)
                                                                                      (coe v1))
                                                                                   (coe v1) (coe v2)
                                                                                   (coe v3)
                                                                                   (coe v8)))))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2028
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   d_ir'45'to'45'trace''_12
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                      (coe v9)
                                                                                      (coe v1))
                                                                                   (coe v1) (coe v2)
                                                                                   (coe v3)
                                                                                   (coe v8))))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                                                             (coe
                                                                                addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                      (coe
                                                                                         d_ir'45'to'45'trace''_12
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                            (coe v9)
                                                                                            (coe
                                                                                               v1))
                                                                                         (coe v1)
                                                                                         (coe v2)
                                                                                         (coe v3)
                                                                                         (coe
                                                                                            v8)))))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'load'45'count_442))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                            (coe (0 :: Integer)))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              d_ir'45'to'45'trace''_12
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                 (coe v9) (coe v1))
                                                              (coe v1) (coe v2) (coe v3) (coe v8))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                                           (coe (2 :: Integer)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                              (coe
                                                                 addInt (coe (1 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                    (coe
                                                                       d_ir'45'to'45'trace''_12
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                          (coe v9) (coe v1))
                                                                       (coe v1) (coe v2) (coe v3)
                                                                       (coe v8)))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                                                    (coe (0 :: Integer)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                d_ir'45'to'45'trace''_12
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                   (coe v9)
                                                                                   (coe v1))
                                                                                (coe v1) (coe v2)
                                                                                (coe v3) (coe v8))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                                (coe
                                                                                   addInt
                                                                                   (coe
                                                                                      (1 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                      (coe
                                                                                         d_ir'45'to'45'trace''_12
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                            (coe v9)
                                                                                            (coe
                                                                                               v1))
                                                                                         (coe v1)
                                                                                         (coe v2)
                                                                                         (coe v3)
                                                                                         (coe
                                                                                            v8)))))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_ir'45'to'45'trace''_12
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                    (coe v9) (coe v1))
                                                                 (coe v1) (coe v2) (coe v3)
                                                                 (coe v8)))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                                              (coe
                                                                 addInt (coe (4 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                       (coe
                                                                          d_ir'45'to'45'trace''_12
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                             (coe v9) (coe v1))
                                                                          (coe v1) (coe v2) (coe v3)
                                                                          (coe v8)))))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                              (coe
                                                                 MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2030
                                                                 (coe
                                                                    addInt (coe (5 :: Integer))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                          (coe
                                                                             d_ir'45'to'45'trace''_12
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                (coe v9) (coe v1))
                                                                             (coe v1) (coe v2)
                                                                             (coe v3) (coe v8)))))))
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                (coe
                                                                                   d_ir'45'to'45'trace''_12
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                      (coe v9)
                                                                                      (coe v1))
                                                                                   (coe v1) (coe v2)
                                                                                   (coe v3)
                                                                                   (coe v8))))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'alloc'45'heap_2098
                                                                                (coe
                                                                                   (2 :: Integer)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                (coe
                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2050
                                                                                   (coe
                                                                                      addInt
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                         (coe
                                                                                            d_ir'45'to'45'trace''_12
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                               (coe
                                                                                                  v9)
                                                                                               (coe
                                                                                                  v1))
                                                                                            (coe v1)
                                                                                            (coe v2)
                                                                                            (coe v3)
                                                                                            (coe
                                                                                               v8)))))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'tag'45'lit_2094
                                                                                         (coe
                                                                                            (1 ::
                                                                                               Integer)))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect_2052)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                  (coe
                                                                                                     d_ir'45'to'45'trace''_12
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                                        (coe
                                                                                                           v9)
                                                                                                        (coe
                                                                                                           v1))
                                                                                                     (coe
                                                                                                        v1)
                                                                                                     (coe
                                                                                                        v2)
                                                                                                     (coe
                                                                                                        v3)
                                                                                                     (coe
                                                                                                        v8))))
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'indirect'45'suc_2054)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2048
                                                                                                     (coe
                                                                                                        addInt
                                                                                                        (coe
                                                                                                           (1 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                           (coe
                                                                                                              d_ir'45'to'45'trace''_12
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                                                 (coe
                                                                                                                    v9)
                                                                                                                 (coe
                                                                                                                    v1))
                                                                                                              (coe
                                                                                                                 v1)
                                                                                                              (coe
                                                                                                                 v2)
                                                                                                              (coe
                                                                                                                 v3)
                                                                                                              (coe
                                                                                                                 v8)))))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'input_2038)
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      d_ir'45'to'45'trace''_12
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                         (coe v9)
                                                                                         (coe v1))
                                                                                      (coe v1)
                                                                                      (coe v2)
                                                                                      (coe v3)
                                                                                      (coe v8)))))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'reg'45'op_2102
                                                                                (coe
                                                                                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_scratch'45'dec_440))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2028
                                                                       (coe
                                                                          addInt
                                                                          (coe (4 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                (coe
                                                                                   d_ir'45'to'45'trace''_12
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                      (coe v9)
                                                                                      (coe v1))
                                                                                   (coe v1) (coe v2)
                                                                                   (coe v3)
                                                                                   (coe v8)))))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2104
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2026
                                                                          (coe
                                                                             addInt
                                                                             (coe (5 :: Integer))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                   (coe
                                                                                      d_ir'45'to'45'trace''_12
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158
                                                                                         (coe v9)
                                                                                         (coe v1))
                                                                                      (coe v1)
                                                                                      (coe v2)
                                                                                      (coe v3)
                                                                                      (coe v8)))))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      d_ir'45'to'45'trace''_12
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_158 (coe v9)
                                         (coe v1))
                                      (coe v1) (coe v2) (coe v3) (coe v8)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.IR.C_Para_380 v6 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_Out_384 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_in'45'ν_388 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_Ana_394 v6 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_Hylo_402 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_Fuse_410 v5 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_free'45'heap_412 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_mov'45'to'45'output_2036)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_const_416 v6 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'load'45'const_2088
                         (coe v1) (coe v6) (coe v8))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'sigop_2084 (coe v0)
                         (coe v1) (coe v7))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.proj-trace
d_proj'45'trace_348 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2034]
d_proj'45'trace_348 v0
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
d_proj'45'bodies_352 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_proj'45'bodies_352 v0
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
d_proj'45'budget_356 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Integer
d_proj'45'budget_356 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.IRToTrace.ir-to-trace
d_ir'45'to'45'trace_364 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2034]
d_ir'45'to'45'trace_364 v0 v1 v2
  = coe
      d_proj'45'trace_348
      (coe
         d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-at-frontier
d_ir'45'to'45'trace'45'at'45'frontier_372 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2034]
d_ir'45'to'45'trace'45'at'45'frontier_372 v0 v1 v2 v3
  = coe
      d_proj'45'trace_348
      (coe
         d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe v2)
         (coe (0 :: Integer)) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget
d_ir'45'stack'45'budget_382 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_ir'45'stack'45'budget_382 v0 v1 v2
  = coe
      d_proj'45'budget_356
      (coe
         d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies
d_ir'45'to'45'bodies_390 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ir'45'to'45'bodies_390 v0 v1 v2
  = coe
      d_proj'45'bodies_352
      (coe
         d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe (0 :: Integer)) (coe v2))
-- Once.CCC.Codegen.IRToTrace.ir-to-trace-from
d_ir'45'to'45'trace'45'from_398 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'trace'45'from_398 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
               (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
                  (coe v2) (coe v3)))))
-- Once.CCC.Codegen.IRToTrace.ir-stack-budget-from
d_ir'45'stack'45'budget'45'from_412 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Integer
d_ir'45'stack'45'budget'45'from_412 v0 v1 v2 v3
  = coe
      d_proj'45'budget_356
      (coe
         d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
         (coe v2) (coe v3))
-- Once.CCC.Codegen.IRToTrace.ir-to-bodies-from
d_ir'45'to'45'bodies'45'from_422 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ir'45'to'45'bodies'45'from_422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
               (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  d_ir'45'to'45'trace''_12 (coe v0) (coe v1) (coe (0 :: Integer))
                  (coe v2) (coe v3)))))
