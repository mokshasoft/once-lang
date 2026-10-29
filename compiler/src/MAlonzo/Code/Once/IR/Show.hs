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

module MAlonzo.Code.Once.IR.Show where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Name
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal

-- Once.IR.Show.showDecimal
d_showDecimal_6 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showDecimal_6 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Data.Integer.Show.d_show_6
         (coe MAlonzo.Code.Once.Spec.Float.Decimal.d_sig_14 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("e-" :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.Nat.Show.d_show_56
            (MAlonzo.Code.Once.Spec.Float.Decimal.d_exp10_16 (coe v0))))
-- Once.IR.Show.showIR
d_showIR_14 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showIR_14 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe ("id" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C__'8728'__28 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_showArg_20 (coe v4) (coe v1) (coe v6))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (" . " :: Data.Text.Text)
                (d_showArg_20 (coe v0) (coe v4) (coe v7)))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("<" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showIR_14 (coe v0) (coe v8) (coe v6))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_showIR_14 (coe v0) (coe v9) (coe v7)) (">" :: Data.Text.Text))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe ("fst" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_snd_48 -> coe ("snd" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_inl_54 -> coe ("inl" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_inr_60 -> coe ("inr" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_case_68 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("[" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showIR_14 (coe v8) (coe v1) (coe v6))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (", " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (d_showIR_14 (coe v9) (coe v1) (coe v7)) ("]" :: Data.Text.Text))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe ("terminal" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe ("initial" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_curry_84 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v7 v8
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("curry(" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showIR_14
                          (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v7)) (coe v8)
                          (coe v6))
                       (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90 -> coe ("apply" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_In_94 v4 -> coe ("In" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v4
        -> coe ("out-mu" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_Cata_106 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("cata(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showIR_14
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10)
                                       (coe v1)))
                                 (coe v1) (coe v7))
                              (")" :: Data.Text.Text))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v4 -> coe ("Out" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v4
        -> coe ("in-nu" :: Data.Text.Text)
      MAlonzo.Code.Once.IR.C_Ana_122 v4 v7
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("ana(" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showIR_14
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v10)
                                    (coe v9))
                                 (coe v7))
                              (")" :: Data.Text.Text))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v6
        -> case coe v0 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v7 v8
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("iter(" :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_showIR_14
                          (coe v0) (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v8))
                          (coe v6))
                       (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_516
               -> coe MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v5)
             MAlonzo.Code.Once.IRTy.C_fits'45'float_518
               -> coe d_showDecimal_6 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_140 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("sigop " :: Data.Text.Text)
             (MAlonzo.Code.Once.Name.d_showCanonical_4
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v5)))
      MAlonzo.Code.Once.IR.C_Call_146 v5
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("call " :: Data.Text.Text)
             (MAlonzo.Code.Once.Name.d_showCanonical_4 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Show.showArg
d_showArg_20 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArg_20 v0 v1 v2
  = let v3 = d_showIR_14 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.IR.C__'8728'__28 v5 v7 v8
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("(" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_showIR_14
                      (coe v0) (coe v1)
                      (coe MAlonzo.Code.Once.IR.C__'8728'__28 v5 v7 v8))
                   (")" :: Data.Text.Text))
         _ -> coe v3)
