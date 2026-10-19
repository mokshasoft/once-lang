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

module MAlonzo.Code.Once.Warnings where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Warnings.ExactQ
d_ExactQ_4 = ()
data T_ExactQ_4 = C__'47'Q__14 Integer Integer
-- Once.Warnings.ExactQ.num
d_num_10 :: T_ExactQ_4 -> Integer
d_num_10 v0
  = case coe v0 of
      C__'47'Q__14 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.ExactQ.den
d_den_12 :: T_ExactQ_4 -> Integer
d_den_12 v0
  = case coe v0 of
      C__'47'Q__14 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.Warning
d_Warning_16 = ()
data T_Warning_16
  = C_FloatRounded_32 Integer Integer Integer Integer Integer
                      T_ExactQ_4 T_ExactQ_4 |
    C_FloatOverflow_42 Integer Integer Integer Integer |
    C_FloatUnderflow_52 Integer Integer Integer Integer |
    C_SilentRound_56 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Warnings.posPart
d_posPart_58 :: Integer -> Integer
d_posPart_58 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe (0 :: Integer)
-- Once.Warnings.negPart
d_negPart_60 :: Integer -> Integer
d_negPart_60 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe (0 :: Integer)
      _ -> coe subInt (coe (0 :: Integer)) (coe v0)
-- Once.Warnings.errorOf
d_errorOf_74 ::
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_errorOf_74 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C__'47'Q__14 (coe d_n_92 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe
            mulInt
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v1))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe du_q_90 (coe v3)))))
      (coe
         C__'47'Q__14 (coe d_n_92 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe
            mulInt
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v1))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe du_p_88 (coe v3)))))
-- Once.Warnings._.p
d_p_88 :: Integer -> Integer -> Integer -> Integer -> Integer
d_p_88 ~v0 ~v1 ~v2 v3 = du_p_88 v3
du_p_88 :: Integer -> Integer
du_p_88 v0 = coe d_posPart_58 (coe v0)
-- Once.Warnings._.q
d_q_90 :: Integer -> Integer -> Integer -> Integer -> Integer
d_q_90 ~v0 ~v1 ~v2 v3 = du_q_90 v3
du_q_90 :: Integer -> Integer
du_q_90 v0 = coe d_negPart_60 (coe v0)
-- Once.Warnings._.n
d_n_92 :: Integer -> Integer -> Integer -> Integer -> Integer
d_n_92 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302
      (coe
         mulInt
         (coe
            mulInt (coe v2)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe du_p_88 (coe v3))))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
            (coe v1)))
      (coe
         mulInt (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe du_q_90 (coe v3))))
-- Once.Warnings.warn-exact
d_warn'45'exact_94 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_ExactQ_4 -> T_ExactQ_4 -> Maybe T_Warning_16
d_warn'45'exact_94 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C__'47'Q__14 v7 v8
        -> let v9
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        C_FloatRounded_32 (coe v0) (coe v1) (coe v2) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176 (coe v4)
                           (coe
                              MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v0)
                              (coe v1) (coe v2)))
                        (coe v5) (coe v6)) in
           coe
             (case coe v7 of
                0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ | coe geqInt (coe v7) (coe (0 :: Integer)) -> coe v9
                _ -> coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.warn-under
d_warn'45'under_122 ::
  Integer ->
  Integer -> Integer -> Integer -> Integer -> Maybe T_Warning_16
d_warn'45'under_122 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_FloatUnderflow_52 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Warnings.warn-hi
d_warn'45'hi_140 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Bool -> Maybe T_Warning_16
d_warn'45'hi_140 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_FloatOverflow_42 (coe v0) (coe v1) (coe v2) (coe v3))
      else coe
             d_warn'45'exact_94 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe d_errorOf_74 (coe v5) (coe v2) (coe v6) (coe v7)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_errorOf_74 (coe v5) (coe v2) (coe v6) (coe v7)))
-- Once.Warnings.warn-at
d_warn'45'at_174 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer -> Maybe T_Warning_16
d_warn'45'at_174 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      0 -> coe
             d_warn'45'under_122 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      _ | coe geqInt (coe v8) (coe (1 :: Integer)) ->
          coe
            d_warn'45'hi_140 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
            (coe v5) (coe v6) (coe v7)
            (coe
               ltInt
               (coe
                  MAlonzo.Code.Once.Spec.Float.Decimal.d_maxFiniteExp_98 (coe v4))
               (coe v8))
      _ -> coe
             d_warn'45'under_122 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
-- Once.Warnings.floatWarning
d_floatWarning_226 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer -> Maybe T_Warning_16
d_floatWarning_226 v0 v1 v2 v3 v4
  = coe
      d_warn'45'at_174 (coe v1) (coe v2) (coe v3) (coe v4) (coe v0)
      (coe du_sig_242 (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
            (coe du_sig_242 (coe v1) (coe v2) (coe v3)) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
            (coe du_sig_242 (coe v1) (coe v2) (coe v3)) (coe v3)))
      (coe
         MAlonzo.Code.Once.Spec.Float.Decimal.d_storedExp_90 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
               (coe du_sig_242 (coe v1) (coe v2) (coe v3)) (coe v3)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Once.Spec.Float.Decimal.d_roundSig_68 (coe v0)
               (coe du_sig_242 (coe v1) (coe v2) (coe v3)) (coe v3))))
-- Once.Warnings._.sig
d_sig_242 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer -> Integer
d_sig_242 ~v0 v1 v2 v3 ~v4 = du_sig_242 v1 v2 v3
du_sig_242 :: Integer -> Integer -> Integer -> Integer
du_sig_242 v0 v1 v2
  = coe
      addInt
      (coe
         mulInt (coe v0)
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
            (coe v2)))
      (coe v1)
-- Once.Warnings.rawFloatLits
d_rawFloatLits_244 ::
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_rawFloatLits_244 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawFloatLits_244 (coe v1)) (coe d_rawFloatLits_244 (coe v2))
      MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v1 v2
        -> coe d_rawFloatLits_244 (coe v2)
      MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawFloatLits_244 (coe v2)) (coe d_rawFloatLits_244 (coe v3))
      MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawFloatLits_244 (coe v1)) (coe d_rawFloatLits_244 (coe v2))
      MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawFloatLits_244 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe d_rawFloatLits_244 (coe v3))
                (coe d_rawFloatLits_244 (coe v5)))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Lang.Syntax.C_RStringLit_58 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v1 v2
        -> coe d_rawFloatLits_244 (coe v1)
      MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_rawFloatLits_244 (coe v2)) (coe d_rawFloatLits_244 (coe v3))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v2
        -> coe d_rawFloatLits_244 (coe v2)
      MAlonzo.Code.Once.Lang.Syntax.C_RAna_66 v1 v2
        -> coe d_rawFloatLits_244 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.declFloatLits
d_declFloatLits_284 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_declFloatLits_284 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_22 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 v1 v2
        -> coe d_rawFloatLits_244 (coe v2)
      MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_28 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.moduleFloatLits
d_moduleFloatLits_288 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_moduleFloatLits_288 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 v1
        -> coe du_go_296 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings._.go
d_go_296 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_296 ~v0 v1 = du_go_296 v1
du_go_296 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_296 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_declFloatLits_284 (coe v1)) (coe du_go_296 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.roundingWarnings
d_roundingWarnings_302 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> [T_Warning_16]
d_roundingWarnings_302 v0 v1
  = coe
      d_go_314 (coe v0) (coe v1) (coe d_moduleFloatLits_288 (coe v1))
-- Once.Warnings._.F
d_F_312 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_F_312 v0 ~v1 = du_F_312 v0
du_F_312 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
du_F_312 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.d_arch'45'float'45'format_68 (coe v0)
-- Once.Warnings._.go
d_go_314 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Warning_16]
d_go_314 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  du_keep_330 (coe v0) (coe v1) (coe v4)
                                  (coe
                                     d_floatWarning_226 (coe du_F_312 (coe v0)) (coe v5) (coe v7)
                                     (coe v9) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings._._.keep
d_keep_330 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe T_Warning_16 -> [T_Warning_16]
d_keep_330 v0 v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_keep_330 v0 v1 v6 v7
du_keep_330 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe T_Warning_16 -> [T_Warning_16]
du_keep_330 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
             (coe d_go_314 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_go_314 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.showQ
d_showQ_352 ::
  T_ExactQ_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQ_352 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe d_num_10 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("/" :: Data.Text.Text)
         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 (d_den_12 (coe v0))))
-- Once.Warnings.zeros
d_zeros_356 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_zeros_356 v0
  = case coe v0 of
      0 -> coe ("" :: Data.Text.Text)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("0" :: Data.Text.Text) (d_zeros_356 (coe v1)))
-- Once.Warnings.showFrac
d_showFrac_360 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFrac_360 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_zeros_356
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (MAlonzo.Code.Data.String.Base.d_length_22
               (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0))))
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.Warnings.showLit
d_showLit_366 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLit_366 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("." :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_showFrac_360 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (" (" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                  (" frac digits)" :: Data.Text.Text)))))
-- Once.Warnings.renderWarning
d_renderWarning_374 ::
  T_Warning_16 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderWarning_374 v0
  = case coe v0 of
      C_FloatRounded_32 v1 v2 v3 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: float literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLit_366 (coe v1) (coe v2) (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" at offset " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" is not exact at this target; stored as 0x-pattern "
                          ::
                          Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (", absolute error " :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (d_showQ_352 (coe v6))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (", " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (d_showQ_352 (coe v7)) (" ulp" :: Data.Text.Text))))))))))
      C_FloatOverflow_42 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: float literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLit_366 (coe v1) (coe v2) (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" at offset " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                      (" is too large for this target's format; stored as infinity"
                       ::
                       Data.Text.Text))))
      C_FloatUnderflow_52 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: float literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLit_366 (coe v1) (coe v2) (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" at offset " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" is too small for this target's format; stored as zero"
                          ::
                          Data.Text.Text)
                         (" (Once models no subnormals)" :: Data.Text.Text)))))
      C_SilentRound_56 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: a loop in `" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("` runs a round that performs no event;" :: Data.Text.Text)
                   (" if the loop never ends, the program goes silent"
                    ::
                    Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.loopWarnings
d_loopWarnings_408 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> [T_Warning_16]
d_loopWarnings_408 v0
  = coe
      du_go_416
      (coe MAlonzo.Code.Once.Compile.d_silentRoundDefs_832 (coe v0))
-- Once.Warnings._.go
d_go_416 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
d_go_416 ~v0 v1 = du_go_416 v1
du_go_416 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
du_go_416 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_SilentRound_56 (coe v1)) (coe du_go_416 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.warningsFor
d_warningsFor_422 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_warningsFor_422 v0 v1
  = coe
      du_go_432
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe d_roundingWarnings_302 (coe v0) (coe v1))
         (coe d_loopWarnings_408 (coe v1)))
-- Once.Warnings._.go
d_go_432 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [T_Warning_16] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_go_432 ~v0 ~v1 v2 = du_go_432 v2
du_go_432 ::
  [T_Warning_16] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_go_432 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_renderWarning_374 (coe v1)) (coe du_go_432 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
