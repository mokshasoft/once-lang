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

module MAlonzo.Code.Once.Escape where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Escape.escape-compose
d_escape'45'compose_10 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> MAlonzo.Code.Once.IR.T_IR_10
d_escape'45'compose_10 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Once.IR.C__'8728'__22 v1 v3 v4 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C__'8728'__22 v7 v9 v10
           -> case coe v10 of
                MAlonzo.Code.Once.IR.C_fst_28
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v13 v14
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v18 v19 v20
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__22
                                     (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v7) (coe v14))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__22 v7 v9
                                        (coe MAlonzo.Code.Once.IR.C_fst_28))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v18 v19
                                        (coe MAlonzo.Code.Once.IR.C_Stack_6))
                              _ -> coe v5
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_snd_34
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v13 v14
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v18 v19 v20
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__22
                                     (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v13) (coe v7))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__22 v7 v9
                                        (coe MAlonzo.Code.Once.IR.C_snd_34))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v18 v19
                                        (coe MAlonzo.Code.Once.IR.C_Stack_6))
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fst_28
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v13 v14 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22
                              (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v2) (coe v9))
                              (coe MAlonzo.Code.Once.IR.C_fst_28)
                              (coe
                                 MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v13 v14
                                 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_snd_34
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v8 v9
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v13 v14 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22
                              (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v8) (coe v2))
                              (coe MAlonzo.Code.Once.IR.C_snd_34)
                              (coe
                                 MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v13 v14
                                 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_inl_48 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22
                              (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v12))
                              (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v9 v10)
                              (coe
                                 MAlonzo.Code.Once.IR.C_inl_48 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       MAlonzo.Code.Once.IR.C_inr_54 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22
                              (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v11) (coe v0))
                              (coe MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v9 v10)
                              (coe
                                 MAlonzo.Code.Once.IR.C_inr_54 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_terminal_66
           -> case coe v4 of
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v10 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__38 v13 v14
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22 v1
                              (coe MAlonzo.Code.Once.IR.C_terminal_66)
                              (coe
                                 MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v10 v11
                                 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       _ -> coe v5
                MAlonzo.Code.Once.IR.C_curry_80 v11 v12
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v13 v14 v15
                         -> coe
                              MAlonzo.Code.Once.IR.C__'8728'__22 v1
                              (coe MAlonzo.Code.Once.IR.C_terminal_66)
                              (coe
                                 MAlonzo.Code.Once.IR.C_curry_80 v11
                                 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_apply_88
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
                         -> case coe v4 of
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v17 v18 v19
                                -> case coe v17 of
                                     MAlonzo.Code.Once.IR.C_id_14
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__22
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v11) (coe v12) (coe v2))
                                               (coe v11))
                                            (coe MAlonzo.Code.Once.IR.C_apply_88)
                                            (coe
                                               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                               (coe MAlonzo.Code.Once.IR.C_id_14) v18
                                               (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                     MAlonzo.Code.Once.IR.C__'8728'__22 v21 v23 v24
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__22
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v11) (coe v12) (coe v2))
                                               (coe v11))
                                            (coe MAlonzo.Code.Once.IR.C_apply_88)
                                            (coe
                                               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                               (coe MAlonzo.Code.Once.IR.C__'8728'__22 v21 v23 v24)
                                               v18 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                     MAlonzo.Code.Once.IR.C_fst_28
                                       -> case coe v0 of
                                            MAlonzo.Code.Once.Type.C__'42'__38 v22 v23
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__22
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'42'__38
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                         (coe v11) (coe v12) (coe v2))
                                                      (coe v11))
                                                   (coe MAlonzo.Code.Once.IR.C_apply_88)
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                                      (coe MAlonzo.Code.Once.IR.C_fst_28) v18
                                                      (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                            _ -> coe v5
                                     MAlonzo.Code.Once.IR.C_snd_34
                                       -> case coe v0 of
                                            MAlonzo.Code.Once.Type.C__'42'__38 v22 v23
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__22
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'42'__38
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                         (coe v11) (coe v12) (coe v2))
                                                      (coe v11))
                                                   (coe MAlonzo.Code.Once.IR.C_apply_88)
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                                      (coe MAlonzo.Code.Once.IR.C_snd_34) v18
                                                      (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                            _ -> coe v5
                                     MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v23 v24
                                       -> case coe v0 of
                                            MAlonzo.Code.Once.Type.C__'43'__40 v25 v26
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__22
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'42'__38
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                         (coe v11) (coe v12) (coe v2))
                                                      (coe v11))
                                                   (coe MAlonzo.Code.Once.IR.C_apply_88)
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62
                                                         v23 v24)
                                                      v18 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                            _ -> coe v5
                                     MAlonzo.Code.Once.IR.C_initial_70
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__22
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v11) (coe v12) (coe v2))
                                               (coe v11))
                                            (coe MAlonzo.Code.Once.IR.C_apply_88)
                                            (coe
                                               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                               (coe MAlonzo.Code.Once.IR.C_initial_70) v18
                                               (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                     MAlonzo.Code.Once.IR.C_curry_80 v24 v25
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__22
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v11) (coe v12) (coe v2))
                                               (coe v11))
                                            (coe MAlonzo.Code.Once.IR.C_apply_88)
                                            (coe
                                               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_curry_80 v24
                                                  (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                               v18 (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                     MAlonzo.Code.Once.IR.C_apply_88
                                       -> case coe v0 of
                                            MAlonzo.Code.Once.Type.C__'42'__38 v23 v24
                                              -> case coe v23 of
                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v25 v26 v27
                                                     -> coe
                                                          MAlonzo.Code.Once.IR.C__'8728'__22
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'42'__38
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                                (coe v11) (coe v12) (coe v2))
                                                             (coe v11))
                                                          (coe MAlonzo.Code.Once.IR.C_apply_88)
                                                          (coe
                                                             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                                             (coe MAlonzo.Code.Once.IR.C_apply_88)
                                                             v18
                                                             (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                                   _ -> coe v5
                                            _ -> coe v5
                                     MAlonzo.Code.Once.IR.C_Prim_108 v22
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__22
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__38
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                                                  (coe v11) (coe v12) (coe v2))
                                               (coe v11))
                                            (coe MAlonzo.Code.Once.IR.C_apply_88)
                                            (coe
                                               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                                               (coe MAlonzo.Code.Once.IR.C_Prim_108 v22) v18
                                               (coe MAlonzo.Code.Once.IR.C_Stack_6))
                                     _ -> coe v5
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fold_92
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Fix_46 v7
                  -> case coe v4 of
                       MAlonzo.Code.Once.IR.C_inl_48 v10
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__22
                                     (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v0) (coe v12))
                                     (coe MAlonzo.Code.Once.IR.C_fold_92)
                                     (coe
                                        MAlonzo.Code.Once.IR.C_inl_48
                                        (coe MAlonzo.Code.Once.IR.C_Stack_6))
                              _ -> coe v5
                       MAlonzo.Code.Once.IR.C_inr_54 v10
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__22
                                     (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v11) (coe v0))
                                     (coe MAlonzo.Code.Once.IR.C_fold_92)
                                     (coe
                                        MAlonzo.Code.Once.IR.C_inr_54
                                        (coe MAlonzo.Code.Once.IR.C_Stack_6))
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Escape.escape-once
d_escape'45'once_96 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> MAlonzo.Code.Once.IR.T_IR_10
d_escape'45'once_96 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe MAlonzo.Code.Once.IR.C_id_14
      MAlonzo.Code.Once.IR.C__'8728'__22 v4 v6 v7
        -> coe
             d_escape'45'compose_10 (coe v0) (coe v4) (coe v1)
             (coe d_escape'45'once_96 (coe v4) (coe v1) (coe v6))
             (coe d_escape'45'once_96 (coe v0) (coe v4) (coe v7))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe MAlonzo.Code.Once.IR.C_fst_28
      MAlonzo.Code.Once.IR.C_snd_34 -> coe MAlonzo.Code.Once.IR.C_snd_34
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                    (d_escape'45'once_96 (coe v0) (coe v9) (coe v6))
                    (d_escape'45'once_96 (coe v0) (coe v10) (coe v7)) v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v5
        -> coe MAlonzo.Code.Once.IR.C_inl_48 v5
      MAlonzo.Code.Once.IR.C_inr_54 v5
        -> coe MAlonzo.Code.Once.IR.C_inr_54 v5
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62
                    (d_escape'45'once_96 (coe v8) (coe v1) (coe v6))
                    (d_escape'45'once_96 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66
        -> coe MAlonzo.Code.Once.IR.C_terminal_66
      MAlonzo.Code.Once.IR.C_initial_70
        -> coe MAlonzo.Code.Once.IR.C_initial_70
      MAlonzo.Code.Once.IR.C_curry_80 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_80
                    (d_escape'45'once_96
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v9))
                       (coe v11) (coe v7))
                    v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_88
        -> coe MAlonzo.Code.Once.IR.C_apply_88
      MAlonzo.Code.Once.IR.C_fold_92
        -> coe MAlonzo.Code.Once.IR.C_fold_92
      MAlonzo.Code.Once.IR.C_unfold_96
        -> coe MAlonzo.Code.Once.IR.C_unfold_96
      MAlonzo.Code.Once.IR.C_arr_102
        -> coe MAlonzo.Code.Once.IR.C_arr_102
      MAlonzo.Code.Once.IR.C_Prim_108 v5
        -> coe MAlonzo.Code.Once.IR.C_Prim_108 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Escape.escape-n
d_escape'45'n_128 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_10 -> MAlonzo.Code.Once.IR.T_IR_10
d_escape'45'n_128 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v3
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                d_escape'45'n_128 (coe v0) (coe v1) (coe v4)
                (coe d_escape'45'once_96 (coe v0) (coe v1) (coe v3)))
-- Once.Escape.escape
d_escape_140 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> MAlonzo.Code.Once.IR.T_IR_10
d_escape_140 v0 v1
  = coe d_escape'45'n_128 (coe v0) (coe v1) (coe (10 :: Integer))
