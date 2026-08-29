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

module MAlonzo.Code.Once.Arith.Machine.WordSem where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Shape
import qualified MAlonzo.Code.Once.Arith.Type
import qualified MAlonzo.Code.Once.Float.Arith
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.WordSem.Sem._.Word
d_Word_26 ::
  Integer -> MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 -> ()
d_Word_26 = erased
-- Once.Arith.Machine.WordSem.Sem.eval-arith-W
d_eval'45'arith'45'W_38 ::
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_28 ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Type.T_NumType_6 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_38 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v6
        -> coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v6)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aflit_16 v6
        -> coe
             MAlonzo.Code.Once.Float.Decimal.d_round_174 (coe v1) (coe v6)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_20 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> let v8
                        = MAlonzo.Code.Once.Arith.Machine.Shape.d_project_34
                            (coe v2) (coe v7) (coe v5) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                         -> coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v9)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe (0 :: Integer))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> let v8
                        = MAlonzo.Code.Once.Arith.Machine.Shape.d_projectF_52
                            (coe v2) (coe v7) (coe v5) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9 -> coe v9
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_24 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Float.Arith.d_fadd_314 (coe v1)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_28 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Float.Arith.d_fsub_316 (coe v1)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_32 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Float.Arith.d_fmul_318 (coe v1)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_36 v7 v8
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Word.d__'47''738'__120 (coe v0)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Float.Arith.d_fdiv_320 (coe v1)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v8) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_38 v6 v7
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__126 (coe v0)
             (coe
                d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v5))
             (coe
                d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v7) (coe v5))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_42 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Arith.Type.C_NInt_8
               -> coe
                    MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
             MAlonzo.Code.Once.Arith.Type.C_NFloat_10
               -> coe
                    MAlonzo.Code.Once.Float.Arith.d_fneg_356 (coe v1)
                    (coe
                       d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Arith.Machine.IR.C_ai2f_44 v6
        -> coe
             MAlonzo.Code.Once.Float.Arith.d_i2f_362 (coe v1)
             (coe
                MAlonzo.Code.Once.Word.d_toℤ_50 (coe v0)
                (coe
                   d_eval'45'arith'45'W_38 (coe v0) (coe v1) (coe v2)
                   (coe MAlonzo.Code.Once.Arith.Type.C_NInt_8) (coe v6) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
