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
import qualified MAlonzo.Code.Once.Postulates
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_8 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32
d_'10214'_'10215''7580'_8 ~v0 v1 = du_'10214'_'10215''7580'_8 v1
du_'10214'_'10215''7580'_8 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32
du_'10214'_'10215''7580'_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_34
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__38
             (coe du_'10214'_'10215''7580'_8 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.proj
d_proj_22 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_4
d_proj_22 ~v0 v1 v2 = du_proj_22 v1 v2
du_proj_22 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_4
du_proj_22 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_36
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20
                    (coe du_'10214'_'10215''7580'_8 (coe v3))
                    (coe du_proj_22 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_28)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_42 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_swap''_42 ~v0 ~v1 = du_swap''_42
du_swap''_42 :: MAlonzo.Code.Once.IR.T_IR_4
du_swap''_42
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
      (coe MAlonzo.Code.Once.IR.C_snd_36)
      (coe MAlonzo.Code.Once.IR.C_fst_28)
-- Once.Surface.Elaborate.distribute
d_distribute_50 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_distribute_50 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__20
      (coe
         MAlonzo.Code.Once.Type.C__'42'__38
         (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_68 (coe v0) (coe v1) (coe v2)) (coe du_swap''_42)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_62 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryInlSwap_62 v0 v1 ~v2 = du_curryInlSwap_62 v0 v1
du_curryInlSwap_62 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
du_curryInlSwap_62 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_94
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__20
         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swap''_42))
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_64 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryInrSwap_64 v0 ~v1 v2 = du_curryInrSwap_64 v0 v2
du_curryInrSwap_64 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
du_curryInrSwap_64 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_94
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__20
         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_62) (coe du_swap''_42))
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_66 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_curryDistrib_66 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
      (coe du_curryInlSwap_62 (coe v0) (coe v1))
      (coe du_curryInrSwap_64 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_68 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_4
d_distrib''_68 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__20
      (coe
         MAlonzo.Code.Once.Type.C__'42'__38
         (coe
            MAlonzo.Code.Once.Type.d__'8658'__64 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C__'43'__40
               (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_102)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__20
            (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v2))
            (d_curryDistrib_66 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_28))
         (coe MAlonzo.Code.Once.IR.C_snd_36))
-- Once.Surface.Elaborate.elaborate
d_elaborate_76 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.IR.T_IR_4
d_elaborate_76 ~v0 v1 v2 v3 = du_elaborate_76 v1 v2 v3
du_elaborate_76 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.IR.T_IR_4
du_elaborate_76 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v5
        -> coe du_proj_22 (coe v0) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Postulates.d_coerceIRArrow_40 erased
                    (coe du_'10214'_'10215''7580'_8 (coe v0)) v9 v11
                    (coe MAlonzo.Code.Once.Type.C_Many_10) v10
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_94
                       (coe
                          du_elaborate_76
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v9
                             (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v11) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_194 v5 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v5) (coe v1))
                (coe v5))
             (coe MAlonzo.Code.Once.IR.C_apply_102)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                (coe
                   MAlonzo.Code.Once.Postulates.d_coerceIRArrow_40 erased
                   (coe du_'10214'_'10215''7580'_8 (coe v0)) v5 v1 v7
                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                   (coe
                      du_elaborate_76 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v5) (coe v7)
                         (coe v1))
                      (coe v8)))
                (coe du_elaborate_76 (coe v0) (coe v5) (coe v9)))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_204 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                    (coe du_elaborate_76 (coe v0) (coe v9) (coe v7))
                    (coe du_elaborate_76 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_214 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v6))
             (coe MAlonzo.Code.Once.IR.C_fst_28)
             (coe
                du_elaborate_76 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v6))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_224 v5 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_36)
             (coe
                du_elaborate_76 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v1))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_234 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20 v8
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe du_elaborate_76 (coe v0) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_244 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__20 v9
                    (coe MAlonzo.Code.Once.IR.C_inr_62)
                    (coe du_elaborate_76 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_256 v5 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                MAlonzo.Code.Once.Type.C__'43'__40
                (coe
                   du_'10214'_'10215''7580'_8
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5)))
                (coe
                   du_'10214'_'10215''7580'_8
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v6))))
             (coe
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_72
                (coe
                   du_elaborate_76
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5))
                   (coe v1) (coe v9))
                (coe
                   du_elaborate_76
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v6))
                   (coe v1) (coe v10)))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__20
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__38
                   (coe du_'10214'_'10215''7580'_8 (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v5) (coe v6)))
                (d_distribute_50
                   (coe du_'10214'_'10215''7580'_8 (coe v0)) (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                   (coe MAlonzo.Code.Once.IR.C_id_10)
                   (coe
                      du_elaborate_76 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v5) (coe v6))
                      (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_262
        -> coe MAlonzo.Code.Once.IR.C_terminal_78
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_270 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe MAlonzo.Code.Once.Type.C_Void_36)
             (coe MAlonzo.Code.Once.IR.C_initial_84)
             (coe
                du_elaborate_76 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_36)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_280 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__20
             (coe
                du_'10214'_'10215''7580'_8
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5)))
             (coe
                du_elaborate_76
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5))
                (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_46
                (coe MAlonzo.Code.Once.IR.C_id_10)
                (coe du_elaborate_76 (coe v0) (coe v5) (coe v7)))
      _ -> MAlonzo.RTE.mazUnreachableError
