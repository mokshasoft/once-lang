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

module MAlonzo.Code.Once.Surface.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_8 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4
d_'10214'_'10215''7580'_8 ~v0 v1 = du_'10214'_'10215''7580'_8 v1
du_'10214'_'10215''7580'_8 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4
du_'10214'_'10215''7580'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_6
      MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__10
             (coe du_'10214'_'10215''7580'_8 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.proj
d_proj_20 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_4
d_proj_20 ~v0 v1 v2 = du_proj_20 v1 v2
du_proj_20 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_4
du_proj_20 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_36
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20
                    (coe du_'10214'_'10215''7580'_8 (coe v3))
                    (coe du_proj_20 (coe v3) (coe v6))
                    (coe MAlonzo.Code.Once.IR.C_fst_28)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_36 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_swap''_36 ~v0 ~v1 = du_swap''_36
du_swap''_36 :: MAlonzo.Code.Once.IR.T_IR_4
du_swap''_36
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
      (coe MAlonzo.Code.Once.IR.C_snd_36)
      (coe MAlonzo.Code.Once.IR.C_fst_28)
-- Once.Surface.Elaborate.distribute
d_distribute_44 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_distribute_44 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__20
      (coe
         MAlonzo.Code.Once.Type.C__'42'__10
         (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_62 (coe v0) (coe v1) (coe v2)) (coe du_swap''_36)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_56 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryInlSwap_56 v0 v1 ~v2 = du_curryInlSwap_56 v0 v1
du_curryInlSwap_56 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
du_curryInlSwap_56 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_94
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__20
         (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swap''_36))
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_58 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryInrSwap_58 v0 ~v1 v2 = du_curryInrSwap_58 v0 v2
du_curryInrSwap_58 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
du_curryInrSwap_58 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_94
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__20
         (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_62) (coe du_swap''_36))
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_60 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryDistrib_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
      (coe du_curryInlSwap_56 (coe v0) (coe v1))
      (coe du_curryInrSwap_58 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_62 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> MAlonzo.Code.Once.IR.T_IR_4
d_distrib''_62 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__20
      (coe
         MAlonzo.Code.Once.Type.C__'42'__10
         (coe
            MAlonzo.Code.Once.Type.C__'8658'__14 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C__'43'__12
               (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_102)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__20
            (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v1) (coe v2))
            (d_curryDistrib_60 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_28))
         (coe MAlonzo.Code.Once.IR.C_snd_36))
-- Once.Surface.Elaborate.elaborate
d_elaborate_70 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.IR.T_IR_4
d_elaborate_70 ~v0 v1 v2 v3 = du_elaborate_70 v1 v2 v3
du_elaborate_70 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.IR.T_IR_4
du_elaborate_70 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v5
        -> coe du_proj_20 (coe v0) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_94
                    (coe
                       du_elaborate_70
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v8) (coe v9)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                MAlonzo.Code.Once.Type.C__'42'__10
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v5) (coe v1))
                (coe v5))
             (coe MAlonzo.Code.Once.IR.C_apply_102)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                (coe
                   du_elaborate_70 (coe v0)
                   (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v5) (coe v1))
                   (coe v7))
                (coe du_elaborate_70 (coe v0) (coe v5) (coe v8)))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                    (coe du_elaborate_70 (coe v0) (coe v9) (coe v7))
                    (coe du_elaborate_70 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v1) (coe v6))
             (coe MAlonzo.Code.Once.IR.C_fst_28)
             (coe
                du_elaborate_70 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v1) (coe v6))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v5 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_36)
             (coe
                du_elaborate_70 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v1))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20 v8
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe du_elaborate_70 (coe v0) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20 v9
                    (coe MAlonzo.Code.Once.IR.C_inr_62)
                    (coe du_elaborate_70 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v5 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                MAlonzo.Code.Once.Type.C__'43'__12
                (coe
                   du_'10214'_'10215''7580'_8
                   (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v5))
                (coe
                   du_'10214'_'10215''7580'_8
                   (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v6)))
             (coe
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                (coe
                   du_elaborate_70
                   (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v5) (coe v1)
                   (coe v9))
                (coe
                   du_elaborate_70
                   (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v6) (coe v1)
                   (coe v10)))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__20
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__10
                   (coe du_'10214'_'10215''7580'_8 (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v5) (coe v6)))
                (d_distribute_44
                   (coe du_'10214'_'10215''7580'_8 (coe v0)) (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                   (coe MAlonzo.Code.Once.IR.C_id_10)
                   (coe
                      du_elaborate_70 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v5) (coe v6))
                      (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.IR.C_terminal_78
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C_Void_8)
             (coe MAlonzo.Code.Once.IR.C_initial_84)
             (coe
                du_elaborate_70 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_8)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                du_'10214'_'10215''7580'_8
                (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v5))
             (coe
                du_elaborate_70
                (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v0 v5) (coe v1)
                (coe v8))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                (coe MAlonzo.Code.Once.IR.C_id_10)
                (coe du_elaborate_70 (coe v0) (coe v5) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
