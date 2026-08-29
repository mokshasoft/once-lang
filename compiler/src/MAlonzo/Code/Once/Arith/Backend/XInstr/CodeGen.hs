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

module MAlonzo.Code.Once.Arith.Backend.XInstr.CodeGen where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax
import qualified MAlonzo.Code.Once.Arith.Machine.AbsInstr
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Arith.Backend.XInstr.CodeGen._≟x_
d__'8799'x__14 ::
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'x__14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.XInstr.CodeGen.abs-reg
d_abs'45'reg_16 ::
  Integer ->
  Maybe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XReg_10
d_abs'45'reg_16 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR0_12)
      1 -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_XR1_14)
      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Once.Arith.Backend.XInstr.CodeGen.path-offset
d_path'45'offset_18 ::
  [MAlonzo.Code.Once.Arith.Machine.Shape.T_Side_24] -> Integer
d_path'45'offset_18 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Arith.Machine.Shape.C_Fst_26
               -> coe d_path'45'offset_18 (coe v2)
             MAlonzo.Code.Once.Arith.Machine.Shape.C_Snd_28
               -> coe
                    addInt (coe (8 :: Integer)) (coe d_path'45'offset_18 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.XInstr.CodeGen.emit
d_emit_28 ::
  MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8 ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
d_emit_28 v0
  = case coe v0 of
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'input_10 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'arg_34
                          (coe v4) (coe v1))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'imm_12 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'imm_26
                          (coe v4) (coe v1))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_add'45'rrr_14 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sub'45'rrr_16 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42
                                                                                      (coe v7))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xadd'45'rr_36
                                                                                         (coe v7)
                                                                                         (coe v8))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsub'45'rr_38
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_mul'45'rrr_18 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Ximul'45'rr_40
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'rrr_20 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'rrr_44
                                              (coe v7) (coe v8) (coe v9))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'rrr_22 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'rrr_46
                                              (coe v7) (coe v8) (coe v9))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_div'45'safe'45'rrr_24 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xdiv'45'safe'45'rrr_48
                                              (coe v7) (coe v8) (coe v9))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_rem'45'safe'45'rrr_26 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xrem'45'safe'45'rrr_50
                                              (coe v7) (coe v8) (coe v9))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_shl'45'rri_28 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xshl'45'rri_52
                                    (coe v6) (coe v7) (coe v3))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_sdiv'45'pow2'45'rri_30 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xsdiv'45'pow2'45'rri_54
                                    (coe v6) (coe v7) (coe v3))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_neg'45'rr_32 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v4 = d_abs'45'reg_16 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                    (coe v5) (coe v6))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xneg'45'r_42
                                       (coe v5))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_spill_34 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'r'45'm_30
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_mk'45'scratch_22
                             (coe v2))
                          (coe v4))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_reload_36 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'm'45'r_32
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_mk'45'scratch_22
                             (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_move'45'to'45'out_38 v1
        -> let v2 = d_abs'45'reg_16 (coe v1) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'out_74
                          (coe v3))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'finput_40 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'farg_72
                          (coe v4) (coe v1))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_load'45'fimm_42 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'fimm_70
                          (coe v4) (coe v1))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fadd'45'rrr_44 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfadd'45'rr_56
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fsub'45'rrr_46 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsubr'45'rr_64
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfsub'45'rr_58
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fmul'45'rrr_48 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> let v10 = d__'8799'x__14 (coe v7) (coe v8) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then coe
                                                            seq (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60
                                                                  (coe v7) (coe v9))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     else coe
                                                            seq (coe v12)
                                                            (let v13
                                                                   = d__'8799'x__14
                                                                       (coe v7) (coe v9) in
                                                             coe
                                                               (case coe v13 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                    -> if coe v14
                                                                         then coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                         else coe
                                                                                seq (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                                                                      (coe v7)
                                                                                      (coe v8))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfmul'45'rr_60
                                                                                         (coe v7)
                                                                                         (coe v9))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fdiv'45'rrr_50 v1 v2 v3
        -> let v4 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v5 = d_abs'45'reg_16 (coe v2) in
              coe
                (let v6 = d_abs'45'reg_16 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                               -> case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfdiv'45'rrr_62
                                              (coe v7) (coe v8) (coe v9))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                             _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                      _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_fneg'45'rr_52 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v4 = d_abs'45'reg_16 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xmov'45'rr_28
                                    (coe v5) (coe v6))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xfneg'45'r_66
                                       (coe v5))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Arith.Machine.AbsInstr.C_i2f'45'rr_54 v1 v2
        -> let v3 = d_abs'45'reg_16 (coe v1) in
           coe
             (let v4 = d_abs'45'reg_16 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.C_Xi2f'45'r_68
                                    (coe v5) (coe v6))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                   _ -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.XInstr.CodeGen.emit-program
d_emit'45'program_870 ::
  [MAlonzo.Code.Once.Arith.Machine.AbsInstr.T_AbstractInstr_8] ->
  [MAlonzo.Code.Once.Arith.Backend.XInstr.Syntax.T_XInstr_24]
d_emit'45'program_870 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_emit_28 (coe v1)) (coe d_emit'45'program_870 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
