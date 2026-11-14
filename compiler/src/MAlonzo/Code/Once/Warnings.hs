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
import qualified MAlonzo.Code.Once.Float.Word
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Float.Dyadic
import qualified MAlonzo.Code.Once.Spec.Float.Value
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
    C_SilentRound_56 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_FloatIdentityEq_60 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Warnings.posPart
d_posPart_62 :: Integer -> Integer
d_posPart_62 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe v0
      _ -> coe (0 :: Integer)
-- Once.Warnings.negPart
d_negPart_64 :: Integer -> Integer
d_negPart_64 v0
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) -> coe (0 :: Integer)
      _ -> coe subInt (coe (0 :: Integer)) (coe v0)
-- Once.Warnings.perUlp
d_perUlp_70 :: T_ExactQ_4 -> Integer -> T_ExactQ_4
d_perUlp_70 v0 v1
  = case coe v0 of
      C__'47'Q__14 v2 v3
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe
                   C__'47'Q__14 (coe v2)
                   (coe
                      mulInt (coe v3)
                      (coe
                         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                         (coe v1)))
             _ -> coe
                    C__'47'Q__14
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2)
                       (coe
                          MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                          (coe subInt (coe (0 :: Integer)) (coe v1))))
                    (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.errorOf
d_errorOf_94 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_errorOf_94 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_absE_114 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         d_perUlp_70 (coe du_absE_114 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4))
-- Once.Warnings._.p
d_p_110 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> Integer
d_p_110 ~v0 ~v1 ~v2 v3 ~v4 = du_p_110 v3
du_p_110 :: Integer -> Integer
du_p_110 v0 = coe d_posPart_62 (coe v0)
-- Once.Warnings._.q
d_q_112 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> Integer
d_q_112 ~v0 ~v1 ~v2 v3 ~v4 = du_q_112 v3
du_q_112 :: Integer -> Integer
du_q_112 v0 = coe d_negPart_64 (coe v0)
-- Once.Warnings._.absE
d_absE_114 ::
  Integer -> Integer -> Integer -> Integer -> Integer -> T_ExactQ_4
d_absE_114 v0 v1 v2 v3 ~v4 = du_absE_114 v0 v1 v2 v3
du_absE_114 ::
  Integer -> Integer -> Integer -> Integer -> T_ExactQ_4
du_absE_114 v0 v1 v2 v3
  = coe
      C__'47'Q__14
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'45'__302
         (coe
            mulInt
            (coe
               mulInt (coe v2)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
                  (coe du_p_110 (coe v3))))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v1)))
         (coe
            mulInt (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
               (coe du_q_112 (coe v3)))))
      (coe
         mulInt
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
            (coe v1))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (2 :: Integer))
            (coe du_q_112 (coe v3))))
-- Once.Warnings.warn-exact
d_warn'45'exact_116 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  T_ExactQ_4 -> T_ExactQ_4 -> Maybe T_Warning_16
d_warn'45'exact_116 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C__'47'Q__14 v7 v8
        -> let v9
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        C_FloatRounded_32 (coe v0) (coe v1) (coe v2) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Float.Word.d_round_58 (coe v4)
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
d_warn'45'under_144 ::
  Integer ->
  Integer -> Integer -> Integer -> Integer -> Maybe T_Warning_16
d_warn'45'under_144 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_FloatUnderflow_52 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Warnings.warn-val
d_warn'45'val_162 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Value.T_FloatVal_24 ->
  Maybe T_Warning_16
d_warn'45'val_162 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'zero_26 v6
        -> coe
             d_warn'45'under_144 (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                addInt
                (coe
                   mulInt (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                      (coe v3)))
                (coe v2))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'num_28 v6 v7 v8
        -> coe
             d_warn'45'exact_116 (coe v1) (coe v2) (coe v3) (coe v4) (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   du_er_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_er_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v8)))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'inf_30 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_FloatOverflow_42 (coe v1) (coe v2) (coe v3) (coe v4))
      MAlonzo.Code.Once.Spec.Float.Value.C_fv'45'nan_32
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings._.er
d_er_212 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Float.Value.T_Sign_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_er_212 v0 v1 v2 v3 ~v4 ~v5 v6 v7 = du_er_212 v0 v1 v2 v3 v6 v7
du_er_212 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_er_212 v0 v1 v2 v3 v4 v5
  = coe
      d_errorOf_94
      (coe
         addInt
         (coe
            mulInt (coe v1)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v3)))
         (coe v2))
      (coe v3) (coe MAlonzo.Code.Once.Spec.Float.Value.d_odd_34 (coe v4))
      (coe v5)
      (coe
         MAlonzo.Code.Once.Spec.Float.Value.d_quantum_70 (coe v0)
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v5)
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
               (MAlonzo.Code.Once.Spec.Float.Dyadic.d_bitLen_74
                  (coe MAlonzo.Code.Once.Spec.Float.Value.d_odd_34 (coe v4)))
               (1 :: Integer))))
-- Once.Warnings.floatWarning
d_floatWarning_214 ::
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30 ->
  Integer -> Integer -> Integer -> Integer -> Maybe T_Warning_16
d_floatWarning_214 v0 v1 v2 v3 v4
  = coe
      d_warn'45'val_162 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Once.Spec.Float.Decimal.d_roundDec_38 (coe v0)
         (coe
            MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v1)
            (coe v2) (coe v3)))
-- Once.Warnings.tokenFloatLits
d_tokenFloatLits_226 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_tokenFloatLits_226 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_tokenFloatLits_226 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TFloat_12 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))))
                       (coe d_tokenFloatLits_226 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.roundingWarnings
d_roundingWarnings_240 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> [T_Warning_16]
d_roundingWarnings_240 v0 v1
  = coe
      d_go_252 (coe v0) (coe v1) (coe d_tokenFloatLits_226 (coe v1))
-- Once.Warnings._.F
d_F_250 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
d_F_250 v0 ~v1 = du_F_250 v0
du_F_250 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Spec.Float.Dyadic.T_FloatFormat_30
du_F_250 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.d_arch'45'float'45'format_68 (coe v0)
-- Once.Warnings._.go
d_go_252 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Warning_16]
d_go_252 v0 v1 v2
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
                                  du_keep_268 (coe v0) (coe v1) (coe v4)
                                  (coe
                                     d_floatWarning_214 (coe du_F_250 (coe v0)) (coe v5) (coe v7)
                                     (coe v9) (coe v10))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings._._.keep
d_keep_268 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe T_Warning_16 -> [T_Warning_16]
d_keep_268 v0 v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_keep_268 v0 v1 v6 v7
du_keep_268 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe T_Warning_16 -> [T_Warning_16]
du_keep_268 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
             (coe d_go_252 (coe v0) (coe v1) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_go_252 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.showQ
d_showQ_294 ::
  T_ExactQ_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQ_294 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe d_num_10 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("/" :: Data.Text.Text)
         (coe MAlonzo.Code.Data.Nat.Show.d_show_56 (d_den_12 (coe v0))))
-- Once.Warnings.zeros
d_zeros_298 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_zeros_298 v0
  = case coe v0 of
      0 -> coe ("" :: Data.Text.Text)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("0" :: Data.Text.Text) (d_zeros_298 (coe v1)))
-- Once.Warnings.showFrac
d_showFrac_302 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFrac_302 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (d_zeros_298
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (MAlonzo.Code.Data.String.Base.d_length_22
               (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0))))
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.Warnings.showLit
d_showLit_308 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLit_308 v0 v1 v2
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         ("." :: Data.Text.Text)
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (d_showFrac_302 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Data.String.Base.d__'43''43'__20
               (" (" :: Data.Text.Text)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                  (" frac digits)" :: Data.Text.Text)))))
-- Once.Warnings.renderWarning
d_renderWarning_316 ::
  T_Warning_16 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_renderWarning_316 v0
  = case coe v0 of
      C_FloatRounded_32 v1 v2 v3 v4 v5 v6 v7
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: float literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLit_308 (coe v1) (coe v2) (coe v3))
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
                                  (d_showQ_294 (coe v6))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (", " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (d_showQ_294 (coe v7)) (" ulp" :: Data.Text.Text))))))))))
      C_FloatOverflow_42 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: float literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_showLit_308 (coe v1) (coe v2) (coe v3))
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
                (d_showLit_308 (coe v1) (coe v2) (coe v3))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" at offset " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                      (" is too small for this target's format; stored as zero"
                       ::
                       Data.Text.Text))))
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
      C_FloatIdentityEq_60 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("warning: `" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("` compares Floats with `==` or `!=`, which is identity"
                    ::
                    Data.Text.Text)
                   (" (NaN == NaN, -0.0 != 0.0); for IEEE equality use `==.` or `!=.`"
                    ::
                    Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.loopWarnings
d_loopWarnings_352 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 -> [T_Warning_16]
d_loopWarnings_352 v0
  = coe
      du_go_360 (coe MAlonzo.Code.Once.Compile.d_silentRoundDefs_1238 v0)
-- Once.Warnings._.go
d_go_360 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
d_go_360 ~v0 v1 = du_go_360 v1
du_go_360 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
du_go_360 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_SilentRound_56 (coe v1)) (coe du_go_360 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.eqWarnings
d_eqWarnings_366 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 -> [T_Warning_16]
d_eqWarnings_366 v0
  = coe
      du_go_374
      (coe MAlonzo.Code.Once.Compile.d_floatIdentityEqDefs_1240 v0)
-- Once.Warnings._.go
d_go_374 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
d_go_374 ~v0 v1 = du_go_374 v1
du_go_374 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> [T_Warning_16]
du_go_374 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe C_FloatIdentityEq_60 (coe v1)) (coe du_go_374 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Warnings.warningsFor
d_warningsFor_380 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_warningsFor_380 v0 v1 v2
  = coe
      du_go_392
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            d_roundingWarnings_240 (coe v0)
            (coe
               MAlonzo.Code.Once.Parser.Lexer.d_tokenize_1084
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe d_loopWarnings_352 (coe v2)) (coe d_eqWarnings_366 (coe v2))))
-- Once.Warnings._.go
d_go_392 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  [T_Warning_16] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_go_392 ~v0 ~v1 ~v2 v3 = du_go_392 v3
du_go_392 ::
  [T_Warning_16] -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_go_392 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_renderWarning_316 (coe v1)) (coe du_go_392 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
