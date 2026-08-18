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

module MAlonzo.Code.Once.Float.Representable where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Float.Representable.supportedFormats
d_supportedFormats_6 ::
  [MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_22]
d_supportedFormats_6
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.Float.Dyadic.d_binary32_34)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Once.Float.Dyadic.d_binary64_36)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Float.Representable.ExactDecimal
d_ExactDecimal_16 a0 a1 a2 a3 = ()
data T_ExactDecimal_16 = C_exact_34
-- Once.Float.Representable.ExactDecimal.shift-is
d_shift'45'is_30 ::
  T_ExactDecimal_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_shift'45'is_30 = erased
-- Once.Float.Representable.ExactDecimal.sig-scaled
d_sig'45'scaled_32 ::
  T_ExactDecimal_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig'45'scaled_32 = erased
-- Once.Float.Representable.storedExp
d_storedExp_36 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_22 ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 -> Integer
d_storedExp_36 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt
         (coe MAlonzo.Code.Once.Float.Dyadic.d_bias_42 (coe v0))
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
            (MAlonzo.Code.Once.Float.Dyadic.d_bitLen_104
               (coe MAlonzo.Code.Once.Float.Dyadic.d_sig_12 (coe v1)))
            (1 :: Integer)))
      (MAlonzo.Code.Once.Float.Dyadic.d_shift_14 (coe v1))
-- Once.Float.Representable.RepresentableAt
d_RepresentableAt_46 a0 a1 = ()
data T_RepresentableAt_46
  = C_representable_64 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                       MAlonzo.Code.Data.Nat.Base.T__'8804'__22
-- Once.Float.Representable.RepresentableAt.mant-fits
d_mant'45'fits_58 ::
  T_RepresentableAt_46 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_mant'45'fits_58 v0
  = case coe v0 of
      C_representable_64 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Representable.RepresentableAt.exp-lo
d_exp'45'lo_60 ::
  T_RepresentableAt_46 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_exp'45'lo_60 v0
  = case coe v0 of
      C_representable_64 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Representable.RepresentableAt.exp-hi
d_exp'45'hi_62 ::
  T_RepresentableAt_46 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_exp'45'hi_62 v0
  = case coe v0 of
      C_representable_64 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Representable.RepresentableAll
d_RepresentableAll_66 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 -> ()
d_RepresentableAll_66 = erased
-- Once.Float.Representable.Accepted
d_Accepted_80 a0 a1 a2 a3 = ()
newtype T_Accepted_80
  = C_accepted_98 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Float.Representable.Accepted.is-exact
d_is'45'exact_94 :: T_Accepted_80 -> T_ExactDecimal_16
d_is'45'exact_94 = erased
-- Once.Float.Representable.Accepted.fits-all
d_fits'45'all_96 ::
  T_Accepted_80 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fits'45'all_96 v0
  = case coe v0 of
      C_accepted_98 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Representable.candidate
d_candidate_106 :: Integer -> Integer -> Integer -> Integer
d_candidate_106 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Nat.Base.du__'47'__318
      (coe
         addInt
         (coe
            mulInt (coe v0)
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
               (coe v2)))
         (coe v1))
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (5 :: Integer))
         (coe v2))
-- Once.Float.Representable.representableAt?
d_representableAt'63'_124 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_22 ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_representableAt'63'_124 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                   (coe
                      MAlonzo.Code.Once.Float.Dyadic.d_bitLen_104
                      (coe MAlonzo.Code.Once.Float.Dyadic.d_sig_12 (coe v1))))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                    (coe
                       MAlonzo.Code.Once.Float.Dyadic.d_bitLen_104
                       (coe MAlonzo.Code.Once.Float.Dyadic.d_sig_12 (coe v1)))
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.Float.Dyadic.d_sig'45'bits_28 (coe v0))))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> let v6
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      (\ v6 ->
                                         coe
                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                           (coe (1 :: Integer)))
                                      (coe
                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                         (coe
                                            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                            (coe (1 :: Integer))
                                            (coe d_storedExp_36 (coe v0) (coe v1)))) in
                            coe
                              (case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                   -> if coe v7
                                        then case coe v8 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                                 -> let v10
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                              (\ v10 ->
                                                                 coe
                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                   (coe
                                                                      d_storedExp_36 (coe v0)
                                                                      (coe v1)))
                                                              (coe
                                                                 MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                              (coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                    (coe
                                                                       d_storedExp_36 (coe v0)
                                                                       (coe v1))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                       (MAlonzo.Code.Data.Nat.Base.d__'94'__276
                                                                          (coe (2 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Once.Float.Dyadic.d_exp'45'bits_30
                                                                             (coe v0)))
                                                                       (2 :: Integer)))) in
                                                    coe
                                                      (case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                           -> if coe v11
                                                                then case coe v12 of
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                                         -> coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v11)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                 (coe
                                                                                    C_representable_64
                                                                                    (coe v5)
                                                                                    (coe v9)
                                                                                    (coe v13)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                else coe
                                                                       seq (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v11)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        else coe
                                               seq (coe v8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                  (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe v3)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Float.Representable.representableAll?
d_representableAll'63'_198 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_representableAll'63'_198 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_all'63'_510
      (coe (\ v1 -> d_representableAt'63'_124 (coe v1) (coe v0)))
      (coe d_supportedFormats_6)
-- Once.Float.Representable.accept-aux
d_accept'45'aux_214 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'45'aux_214 ~v0 ~v1 v2 v3 v4 v5
  = du_accept'45'aux_214 v2 v3 v4 v5
du_accept'45'aux_214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_accept'45'aux_214 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Float.Dyadic.C__'47'2'94'__16
                                                  (coe v1) (coe v0))
                                               (coe C_accepted_98 v8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v7) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v5) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Float.Representable.accept?
d_accept'63'_252 ::
  Integer ->
  Integer -> Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_accept'63'_252 v0 v1 v2
  = coe
      du_accept'45'aux_214 (coe v2)
      (coe d_candidate_106 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe
            mulInt (coe d_candidate_106 (coe v0) (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (5 :: Integer))
               (coe v2)))
         (coe
            addInt
            (coe
               mulInt (coe v0)
               (coe
                  MAlonzo.Code.Data.Nat.Base.d__'94'__276 (coe (10 :: Integer))
                  (coe v2)))
            (coe v1)))
      (coe
         d_representableAll'63'_198
         (coe
            MAlonzo.Code.Once.Float.Dyadic.C__'47'2'94'__16
            (coe d_candidate_106 (coe v0) (coe v1) (coe v2)) (coe v2)))
-- Once.Float.Representable.candidate-recovers
d_candidate'45'recovers_268 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  T_ExactDecimal_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_candidate'45'recovers_268 = erased
-- Once.Float.Representable.dyadic-η
d_dyadic'45'η_290 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dyadic'45'η_290 = erased
-- Once.Float.Representable.exact-irrelevant
d_exact'45'irrelevant_304 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  T_ExactDecimal_16 ->
  T_ExactDecimal_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exact'45'irrelevant_304 = erased
-- Once.Float.Representable.representableAt-irrelevant
d_representableAt'45'irrelevant_330 ::
  MAlonzo.Code.Once.Float.Dyadic.T_FloatFormat_22 ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  T_RepresentableAt_46 ->
  T_RepresentableAt_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_representableAt'45'irrelevant_330 = erased
-- Once.Float.Representable.representableAll-irrelevant
d_representableAll'45'irrelevant_362 ::
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_representableAll'45'irrelevant_362 = erased
-- Once.Float.Representable.accepted-irrelevant
d_accepted'45'irrelevant_392 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  T_Accepted_80 ->
  T_Accepted_80 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_accepted'45'irrelevant_392 = erased
-- Once.Float.Representable.accept?-complete
d_accept'63''45'complete_420 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Float.Dyadic.T_Dyadic_6 ->
  T_Accepted_80 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_accept'63''45'complete_420 = erased
