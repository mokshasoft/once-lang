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

module MAlonzo.Code.Once.IR.Ref where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Type

-- Once.IR.Ref.refIR
d_refIR_8 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_refIR_8 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.IR.C__'8728'__28
              (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe MAlonzo.Code.Once.IR.C_Call_136 v1)
              (coe MAlonzo.Code.Once.IR.C_terminal_72) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Zero_6
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                 (coe MAlonzo.Code.Once.IR.C_Call_136 v1)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       MAlonzo.Code.Once.Type.C_One_8
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                 (coe MAlonzo.Code.Once.IR.C_Call_136 v1)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                 (coe MAlonzo.Code.Once.IR.C_Call_136 v1)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
