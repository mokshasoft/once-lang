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

module MAlonzo.Code.Once.CCC.Machine.ReadTypedAdequate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Machine.Allocation
import qualified MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed
import qualified MAlonzo.Code.Once.CCC.Machine.Locations
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Machine.ReadTypedAdequate._.readTyped
d_readTyped_90 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe AgdaAny
d_readTyped_90 ~v0 ~v1 = du_readTyped_90
du_readTyped_90 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  Maybe AgdaAny
du_readTyped_90
  = coe MAlonzo.Code.Once.CCC.Machine.SMCore.du_readTyped_2556
-- Once.CCC.Machine.ReadTypedAdequate._.ValidAtWF
d_ValidAtWF_138 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.CCC.Machine.ReadTypedAdequate.Readable
d_Readable_172 a0 a1 a2 = ()
data T_Readable_172
  = C_r'45'unit_174 | C_r'45'int_176 |
    C_r'45'pair_182 T_Readable_172 T_Readable_172
-- Once.CCC.Machine.ReadTypedAdequate.readable?
d_readable'63'_186 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 -> Maybe T_Readable_172
d_readable'63'_186 ~v0 ~v1 v2 = du_readable'63'_186 v2
du_readable'63'_186 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> Maybe T_Readable_172
du_readable'63'_186 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_122
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'unit_174)
         MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
           -> let v4 = coe du_readable'63'_186 (coe v2) in
              coe
                (let v5 = coe du_readable'63'_186 (coe v3) in
                 coe
                   (case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                        -> case coe v5 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe C_r'45'pair_182 v6 v7)
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
         MAlonzo.Code.Once.Type.C_Int_136
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_r'45'int_176)
         _ -> coe v1)
-- Once.CCC.Machine.ReadTypedAdequate.subst-×-cong₂
d_subst'45''215''45'cong'8322'_224 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''215''45'cong'8322'_224 = erased
-- Once.CCC.Machine.ReadTypedAdequate.readTyped-adequate
d_readTyped'45'adequate_242 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  T_Readable_172 ->
  MAlonzo.Code.Once.CCC.Machine.Locations.T_ValueLocation_12 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_LocState_482 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AllocState_568 ->
  AgdaAny ->
  MAlonzo.Code.Once.CCC.Machine.ClosureWellFormed.T_ValidAtWF_530 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_readTyped'45'adequate_242 = erased
