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

module MAlonzo.Code.Once.LinCore.MoveCode where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.LinCore.MoveCode.mvSS
d_mvSS_6 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_mvSS_6 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2414
                   (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416
                      (coe v1))
                   (coe
                      d_mvSS_6 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v3))))
-- Once.LinCore.MoveCode.mvSSd
d_mvSSd_18 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_mvSSd_18 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2414
                   (coe addInt (coe v0) (coe v3)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416
                      (coe addInt (coe v1) (coe v3)))
                   (coe d_mvSSd_18 (coe v0) (coe v1) (coe v3))))
-- Once.LinCore.MoveCode.mvPS
d_mvPS_30 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_mvPS_30 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'at_2474 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416
                      (coe v1))
                   (coe
                      d_mvPS_30 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v3))))
-- Once.LinCore.MoveCode.mvSP
d_mvSP_42 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_mvSP_42 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_load'45'from'45'slot_2414
                   (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at_2476 (coe v1))
                   (coe
                      d_mvSP_42 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v3))))
-- Once.LinCore.MoveCode.stores
d_stores_54 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_stores_54 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.CCC.Machine.SMCore.C_store'45'at'45'slot_2416
                   (coe v0))
                (coe
                   d_stores_54 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2)))
-- Once.LinCore.MoveCode.swapMv₃
d_swapMv'8323'_62 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_swapMv'8323'_62 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         d_mvSS_6 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1) (coe v1))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe d_mvSS_6 (coe addInt (coe v0) (coe v1)) (coe v0) (coe v2))
         (coe
            d_mvSS_6 (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1)
            (coe addInt (coe v0) (coe v2)) (coe v1)))
-- Once.LinCore.MoveCode.swapMv
d_swapMv_70 ::
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2404]
d_swapMv_70 v0 v1 v2
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> case coe v2 of
             0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
             _ -> coe d_swapMv'8323'_62 (coe v0) (coe v1) (coe v2)
