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
import qualified MAlonzo.Code.Once.Word

-- Once.Arith.Machine.WordSem.Sem._.Word
d_Word_24 :: Integer -> ()
d_Word_24 = erased
-- Once.Arith.Machine.WordSem.Sem.eval-arith-W
d_eval'45'arith'45'W_32 ::
  Integer ->
  MAlonzo.Code.Once.Arith.Machine.Shape.T_InputShape_8 ->
  MAlonzo.Code.Once.Arith.Machine.IR.T_MArithIR_10 ->
  AgdaAny -> Integer
d_eval'45'arith'45'W_32 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Arith.Machine.IR.C_alit_14 v4
        -> coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v4)
      MAlonzo.Code.Once.Arith.Machine.IR.C_ainput_16 v4
        -> let v5
                 = MAlonzo.Code.Once.Arith.Machine.Shape.d_project_32
                     (coe v1) (coe v4) (coe v3) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                  -> coe MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe v6)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Word.d_fromℤ_20 (coe v0) (coe (0 :: Integer))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Arith.Machine.IR.C_aadd_18 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.d__'8853'__26 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_asub_20 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.d__'8854'__32 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amul_22 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.d__'8855'__38 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_adiv_24 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.d__'47''738'__98 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_amod_26 v4 v5
        -> coe
             MAlonzo.Code.Once.Word.d__'37''738'__104 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v5) (coe v3))
      MAlonzo.Code.Once.Arith.Machine.IR.C_aneg_28 v4
        -> coe
             MAlonzo.Code.Once.Word.d_'8861'__44 (coe v0)
             (coe d_eval'45'arith'45'W_32 (coe v0) (coe v1) (coe v4) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
