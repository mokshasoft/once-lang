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

module MAlonzo.Code.Once.Backend.Common.StackAnalysis where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Backend.Common.StackAnalysis.StackDelta
d_StackDelta_22 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_StackDelta_22 v0 v1 v2 v3 ~v4 v5 v6 v7
  = du_StackDelta_22 v0 v1 v2 v3 v5 v6 v7
du_StackDelta_22 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
du_StackDelta_22 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__22 v8 v10 v11
        -> coe
             addInt
             (coe
                du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v8) (coe v11))
             (coe
                du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8)
                (coe v5) (coe v10))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_34 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v10 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__38 v13 v14
               -> coe
                    addInt
                    (coe
                       addInt
                       (coe
                          du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v13) (coe v10))
                       (coe
                          du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v14) (coe v11)))
                    (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v9 -> coe v1
      MAlonzo.Code.Once.IR.C_inr_54 v9 -> coe v2
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v10 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__40 v12 v13
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe
                       du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v12)
                       (coe v5) (coe v10))
                    (coe
                       du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                       (coe v5) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_70 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_78 v10 v11 -> coe v3
      MAlonzo.Code.Once.IR.C_apply_84 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_fold_88 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_unfold_92 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_98 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_Prim_104 v9 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Backend.Common.StackAnalysis.StackDepth
d_StackDepth_42 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.IR.T_IR_10 -> Integer
d_StackDepth_42 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.IR.C_id_14 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C__'8728'__22 v9 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
             (coe
                d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v9) (coe v12))
             (coe
                addInt
                (coe
                   d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v9) (coe v6) (coe v11))
                (coe
                   du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                   (coe v9) (coe v12)))
      MAlonzo.Code.Once.IR.C_fst_28 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_snd_34 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42 v11 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'42'__38 v14 v15
               -> coe
                    addInt
                    (coe
                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                       (coe
                          d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v14) (coe v11))
                       (coe
                          addInt
                          (coe
                             d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v15) (coe v12))
                          (coe
                             du_StackDelta_22 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                             (coe v14) (coe v11))))
                    (coe v0)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_inl_48 v10 -> coe v1
      MAlonzo.Code.Once.IR.C_inr_54 v10 -> coe v2
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__40 v13 v14
               -> coe
                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                    (coe
                       d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v13) (coe v6) (coe v11))
                    (coe
                       d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v14) (coe v6) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_66 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_initial_70 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_curry_78 v11 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v13 v14 v15
               -> coe
                    addInt
                    (coe
                       d_StackDepth_42 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v13))
                       (coe v15) (coe v11))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_84 -> coe v4
      MAlonzo.Code.Once.IR.C_fold_88 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_unfold_92 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_arr_98 -> coe (0 :: Integer)
      MAlonzo.Code.Once.IR.C_Prim_104 v10 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
