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

module MAlonzo.Code.Once.Arith.Machine.Recognise where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Arith.Machine.AbsState
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Arith.Machine.Recognise.recognise-path
d_recognise'45'path_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22]
d_recognise'45'path_12 v0 ~v1 v2 = du_recognise'45'path_12 v0 v2
du_recognise'45'path_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe [MAlonzo.Code.Once.Arith.Machine.AbsState.T_Side_22]
du_recognise'45'path_12 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.IR.C_id_278
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v4 v6 v7
           -> let v8 = coe du_recognise'45'path_12 (coe v0) (coe v7) in
              coe
                (let v9 = coe du_recognise'45'path_12 (coe v4) (coe v6) in
                 coe
                   (case coe v8 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                        -> case coe v9 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v10)
                                       (coe v11))
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                             _ -> MAlonzo.RTE.mazUnreachableError
                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                      _ -> MAlonzo.RTE.mazUnreachableError))
         MAlonzo.Code.Once.CCC.IR.C_fst_300
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__126 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Arith.Machine.AbsState.C_Fst_24)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> coe v2
         MAlonzo.Code.Once.CCC.IR.C_snd_306
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__126 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Once.Arith.Machine.AbsState.C_Snd_26)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Recognise.recognise-body
d_recognise'45'body_44 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
d_recognise'45'body_44 ~v0 v1 ~v2 v3
  = du_recognise'45'body_44 v1 v3
du_recognise'45'body_44 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10
du_recognise'45'body_44 v0 v1
  = let v2
          = let v2 = coe du_recognise'45'path_12 (coe v0) (coe v1) in
            coe
              (case coe v2 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                   -> coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 (coe v3))
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v4 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.CCC.IR.C_const_416 v9 v10 v11
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C_fits'45'int_194
                         -> let v12 = coe du_is'45'terminal'63'_264 (coe v7) in
                            coe
                              (if coe v12
                                 then coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 (coe v10))
                                 else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       MAlonzo.Code.Once.Type.C_fits'45'float_196
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.CCC.IR.C_SigOp_422 v10
                  -> let v11
                           = let v11
                                   = coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                       erased
                                       (\ v11 ->
                                          coe
                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                            (coe
                                               MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                               (coe v10)))
                                       (coe
                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                          (coe
                                             MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290 (coe v10))
                                          (coe ("arith.neg.int" :: Data.Text.Text))) in
                             coe
                               (case coe v11 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                    -> if coe v12
                                         then coe
                                                seq (coe v13)
                                                (let v14
                                                       = coe
                                                           du_recognise'45'body_44 (coe v0)
                                                           (coe v7) in
                                                 coe
                                                   (case coe v14 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                             (coe
                                                                MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_24
                                                                (coe v15))
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v14
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                         else coe
                                                seq (coe v13)
                                                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294 v15 v16 v17
                            -> case coe v4 of
                                 MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                                   -> let v20
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v20 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe
                                                        MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                        (coe v10)))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe
                                                      MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                      (coe v10))
                                                   (coe ("arith.add.int" :: Data.Text.Text))) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                             -> if coe v21
                                                  then case coe v22 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                           -> let v24
                                                                    = coe
                                                                        du_recognise'45'body_44
                                                                        (coe v0) (coe v15) in
                                                              coe
                                                                (let v25
                                                                       = coe
                                                                           du_recognise'45'body_44
                                                                           (coe v0) (coe v16) in
                                                                 coe
                                                                   (case coe v24 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v26
                                                                        -> case coe v25 of
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18
                                                                                       (coe v26)
                                                                                       (coe v27))
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                               -> coe v25
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v24
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  else coe
                                                         seq (coe v22)
                                                         (let v23
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                    erased
                                                                    (\ v23 ->
                                                                       coe
                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                         (coe
                                                                            MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                                            (coe v10)))
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                       (coe
                                                                          MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                                          (coe v10))
                                                                       (coe
                                                                          ("arith.sub.int"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v23 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                 -> if coe v24
                                                                      then case coe v25 of
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                               -> let v27
                                                                                        = coe
                                                                                            du_recognise'45'body_44
                                                                                            (coe v0)
                                                                                            (coe
                                                                                               v15) in
                                                                                  coe
                                                                                    (let v28
                                                                                           = coe
                                                                                               du_recognise'45'body_44
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  v16) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v27 of
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                                                                                            -> case coe
                                                                                                      v28 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v30
                                                                                                   -> coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20
                                                                                                           (coe
                                                                                                              v29)
                                                                                                           (coe
                                                                                                              v30))
                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                   -> coe
                                                                                                        v28
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                            -> coe
                                                                                                 v27
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      else coe
                                                                             seq (coe v25)
                                                                             (let v26
                                                                                    = coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                        erased
                                                                                        (\ v26 ->
                                                                                           coe
                                                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                                                                (coe
                                                                                                   v10)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.CCC.SigOp.Info.d_name_290
                                                                                              (coe
                                                                                                 v10))
                                                                                           (coe
                                                                                              ("arith.mul.int"
                                                                                               ::
                                                                                               Data.Text.Text))) in
                                                                              coe
                                                                                (case coe v26 of
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                     -> if coe v27
                                                                                          then case coe
                                                                                                      v28 of
                                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v29
                                                                                                   -> let v30
                                                                                                            = coe
                                                                                                                du_recognise'45'body_44
                                                                                                                (coe
                                                                                                                   v0)
                                                                                                                (coe
                                                                                                                   v15) in
                                                                                                      coe
                                                                                                        (let v31
                                                                                                               = coe
                                                                                                                   du_recognise'45'body_44
                                                                                                                   (coe
                                                                                                                      v0)
                                                                                                                   (coe
                                                                                                                      v16) in
                                                                                                         coe
                                                                                                           (case coe
                                                                                                                   v30 of
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v32
                                                                                                                -> case coe
                                                                                                                          v31 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v33
                                                                                                                       -> coe
                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22
                                                                                                                               (coe
                                                                                                                                  v32)
                                                                                                                               (coe
                                                                                                                                  v33))
                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                       -> coe
                                                                                                                            v31
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                -> coe
                                                                                                                     v30
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          else coe
                                                                                                 seq
                                                                                                 (coe
                                                                                                    v28)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> coe v11
                          _ -> coe v11)
                _ -> coe v2
         _ -> coe v2)
-- Once.Arith.Machine.Recognise._.is-terminal?
d_is'45'terminal'63'_264 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
d_is'45'terminal'63'_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_is'45'terminal'63'_264 v7
du_is'45'terminal'63'_264 ::
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> Bool
du_is'45'terminal'63'_264 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.IR.C_terminal_330
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.Arith.Machine.Recognise.recognise
d_recognise_308 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_140
d_recognise_308 v0 v1 ~v2 v3 = du_recognise_308 v0 v1 v3
du_recognise_308 ::
  MAlonzo.Code.Once.Arith.Machine.AbsState.T_InputShape_8 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  Maybe MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_140
du_recognise_308 v0 v1 v2
  = let v3 = coe du_recognise'45'body_44 (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Arith.Machine.IR.C_mk'45'block_150 (coe v0)
                   (coe v4))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
