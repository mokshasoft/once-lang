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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IR.Ref.refIR
d_refIR_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_refIR_10 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.IR.C__'8728'__28
              (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe MAlonzo.Code.Once.IR.C_Call_146 v2)
              (coe MAlonzo.Code.Once.IR.C_terminal_72) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                 (coe MAlonzo.Code.Once.IR.C_Call_146 v2)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       MAlonzo.Code.Once.Spec.Grade.C_One_10
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4))
                                 (coe MAlonzo.Code.Once.IR.C_Call_146 v2)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_84
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4))
                                 (coe MAlonzo.Code.Once.IR.C_Call_146 v2)
                                 (coe MAlonzo.Code.Once.IR.C_snd_48))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
