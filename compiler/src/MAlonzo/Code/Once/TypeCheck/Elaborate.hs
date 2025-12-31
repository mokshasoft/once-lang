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

module MAlonzo.Code.Once.TypeCheck.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Postulates
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.lookup-suc
d_lookup'45'suc_14 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc_14 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc
d_lookup'45'suc'45'suc_38 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc_38 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc_60 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc_60 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc_86 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc_86 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc_116 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc_116 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_150 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_150 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_188 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_188
  = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_230 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_230
  = erased
-- Once.TypeCheck.Elaborate.exchange₈
d_exchange'8328'_276
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.exchange\8328"
-- Once.TypeCheck.Elaborate.weakenFromEmpty
d_weakenFromEmpty_284 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weakenFromEmpty_284 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v3
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v5 v6 v7
        -> let v8 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v9
                    = coe
                        MAlonzo.Code.Once.Postulates.d_coerceQuantity_168 v8 v5 v6 v2
                        (coe MAlonzo.Code.Once.Type.C_Many_10) v7
                        (d_weaken_294
                           (coe v8) (coe v5) (coe v6) (coe v2)
                           (coe d_weakenFromEmpty_284 (coe v8) (coe v5) (coe v2) (coe v3))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Once.Type.C_Many_10
                     -> coe
                          d_weaken_294 (coe v8) (coe v5) (coe v6) (coe v2)
                          (coe d_weakenFromEmpty_284 (coe v8) (coe v5) (coe v2) (coe v3))
                   _ -> coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.weaken
d_weaken_294 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_weaken_294 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_var_170
             (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v7)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange_306
                       (coe v0) (coe v1) (coe v2) (coe v10) (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v7
             (d_weaken_294
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v7) (coe v3))
                (coe v9))
             (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v7) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v9 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                    (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v8 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v8
             (d_weaken_294
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v3) (coe v8))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v7 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v7
             (d_weaken_294
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v7) (coe v3))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v10) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__40 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v7 v8
             (d_weaken_294
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v7) (coe v8))
                (coe v10))
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v11))
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v3) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_weaken_294
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Once.Type.C_Void_36)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v7
             (d_weaken_294 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9))
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange
d_exchange_306 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange_306 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v8
        -> case coe v8 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe
                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                       (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8322'_320
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v13) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v8
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v8) (coe v4))
                (coe v10))
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v10 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'42'__38 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange_306
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
                    (d_exchange_306
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v9
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v4) (coe v9))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v8 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v8
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v8) (coe v4))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange_306
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange_306
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v8 v9
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v8) (coe v9))
                (coe v11))
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v12))
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v4) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v8
             (d_exchange_306
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v10))
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₂
d_exchange'8322'_320 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8322'_320 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v9
        -> case coe v9 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8323'_336
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v14)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v9
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v9) (coe v5))
                (coe v11))
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__38 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8322'_320
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
                    (d_exchange'8322'_320
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v14) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v10
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v10))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v9 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v9
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v9) (coe v5))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__40 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8322'_320
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__40 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8322'_320
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v9 v10 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v9 v10
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v9) (coe v10))
                (coe v12))
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v13))
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10) (coe v5)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v9
             (d_exchange'8322'_320
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v11))
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₃
d_exchange'8323'_336 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8323'_336 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v10
        -> case coe v10 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v12
               -> case coe v12 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v14
                      -> case coe v14 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v16))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8324'_354
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v15) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v10
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v10) (coe v6))
                (coe v12))
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'42'__38 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8323'_336
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
                    (d_exchange'8323'_336
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v15)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v11
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v6) (coe v11))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v10
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v10) (coe v6))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__40 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8323'_336
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__40 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8323'_336
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v10 v11
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v10) (coe v11))
                (coe v13))
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v14))
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v11)
                (coe v6) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v10
             (d_exchange'8323'_336
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v12))
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v13))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₄
d_exchange'8324'_354 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8324'_354 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v11
        -> case coe v11 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v13
               -> case coe v13 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
                      -> case coe v15 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v17
                             -> case coe v17 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v19
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe
                                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                     (coe
                                                        MAlonzo.Code.Data.Fin.Base.C_suc_16 v19)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8325'_374
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v16) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v11
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v11) (coe v7))
                (coe v13))
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v13 v14
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'42'__38 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8324'_354
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
                    (d_exchange'8324'_354
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v12
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v7) (coe v12))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v11 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v11
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v11) (coe v7))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__40 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8324'_354
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__40 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8324'_354
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v11 v12
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v11) (coe v12))
                (coe v14))
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v15))
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v12) (coe v7) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v11
             (d_exchange'8324'_354
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v13))
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v14))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₅
d_exchange'8325'_374 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8325'_374 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v12
        -> case coe v12 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v14
               -> case coe v14 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
                      -> case coe v16 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v20
                                    -> case coe v20 of
                                         MAlonzo.Code.Data.Fin.Base.C_zero_12
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                   (coe
                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                      (coe
                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                         MAlonzo.Code.Data.Fin.Base.C_suc_16 v22
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                   (coe
                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                      (coe
                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                               (coe
                                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                  v22))))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8326'_396
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v15) (coe v17) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v12
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v12) (coe v8))
                (coe v14))
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v14 v15
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'42'__38 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8325'_374
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
                    (d_exchange'8325'_374
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v13
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v8) (coe v13))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v12 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v12
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v12) (coe v8))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__40 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8325'_374
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v15) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__40 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8325'_374
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v12 v13
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v12) (coe v13))
                (coe v15))
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v8) (coe v16))
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v13) (coe v8) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v12
             (d_exchange'8325'_374
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v14))
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v8) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₆
d_exchange'8326'_396 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8326'_396 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v13
        -> case coe v13 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
               -> case coe v15 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v21
                                    -> case coe v21 of
                                         MAlonzo.Code.Data.Fin.Base.C_zero_12
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                   (coe
                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                      (coe
                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                         MAlonzo.Code.Data.Fin.Base.C_suc_16 v23
                                           -> case coe v23 of
                                                MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                  -> coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                       (coe
                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                          (coe
                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                             (coe
                                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                   (coe
                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                                MAlonzo.Code.Data.Fin.Base.C_suc_16 v25
                                                  -> coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                       (coe
                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                          (coe
                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                             (coe
                                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                   (coe
                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                         (coe
                                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                            v25)))))))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (d_exchange'8327'_420
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v16) (coe v18) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v13
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v13) (coe v9))
                (coe v15))
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v15 v16
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'42'__38 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8326'_396
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v17) (coe v15))
                    (d_exchange'8326'_396
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v18) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v14
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v9) (coe v14))
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v13 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v13
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v13) (coe v9))
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'43'__40 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8326'_396
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'43'__40 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8326'_396
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v13 v14
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v13) (coe v14))
                (coe v16))
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v9) (coe v17))
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v14) (coe v9) (coe v18))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe MAlonzo.Code.Once.Type.C_Void_36) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v13
             (d_exchange'8326'_396
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v15))
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v9) (coe v16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₇
d_exchange'8327'_420 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_exchange'8327'_420 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v14
        -> case coe v14 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_170
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
               -> case coe v16 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v18
                      -> case coe v18 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v20
                             -> case coe v20 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v22
                                    -> case coe v22 of
                                         MAlonzo.Code.Data.Fin.Base.C_zero_12
                                           -> coe
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                   (coe
                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                      (coe
                                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                         MAlonzo.Code.Data.Fin.Base.C_suc_16 v24
                                           -> case coe v24 of
                                                MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                  -> coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                       (coe
                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                          (coe
                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                             (coe
                                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                   (coe
                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                      (coe
                                                                         MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                                MAlonzo.Code.Data.Fin.Base.C_suc_16 v26
                                                  -> case coe v26 of
                                                       MAlonzo.Code.Data.Fin.Base.C_zero_12
                                                         -> coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                 (coe
                                                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                    (coe
                                                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                             (coe
                                                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                                                       MAlonzo.Code.Data.Fin.Base.C_suc_16 v28
                                                         -> coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                 (coe
                                                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                    (coe
                                                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                             (coe
                                                                                MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                      v28))))))))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                    (coe
                       d_exchange'8328'_276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v17 v19 v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_190 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_190 v14
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v14) (coe v10))
                (coe v16))
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v14) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v16 v17
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'42'__38 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                    (d_exchange'8327'_420
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v18) (coe v16))
                    (d_exchange'8327'_420
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v19) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_210 v15
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v10) (coe v15))
                (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v14 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_220 v14
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v14) (coe v10))
                (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_230 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                    (d_exchange'8327'_420
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v17) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_240 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'43'__40 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                    (d_exchange'8327'_420
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v18) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v14 v15
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v14) (coe v15))
                (coe v17))
             (coe
                d_exchange'8328'_276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v14 v10 v18)
             (coe
                d_exchange'8328'_276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v15 v10 v19)
      MAlonzo.Code.Once.Surface.Syntax.C_unit_258
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_266 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_266
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe MAlonzo.Code.Once.Type.C_Void_36)
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v14
             (d_exchange'8327'_420
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v14) (coe v16))
             (coe
                d_exchange'8328'_276 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v14 v10 v17)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__786 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__786 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_36
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
               -> let v6 = d__'8799'T__786 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__786 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
               -> let v6 = d__'8799'T__786 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__786 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v5 v6 v7
               -> let v8 = d__'8799'T__786 (coe v2) (coe v5) in
                  coe
                    (let v9
                           = MAlonzo.Code.Once.Type.d__'8799'q__26 (coe v3) (coe v6) in
                     coe
                       (let v10 = d__'8799'T__786 (coe v4) (coe v7) in
                        coe
                          (let v11
                                 = let v11
                                         = case coe v10 of
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                               -> coe
                                                    seq (coe v11)
                                                    (coe
                                                       seq (coe v12)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> case coe v12 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                 -> case coe v13 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v12)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v11
                                               _ -> coe v11
                                        _ -> MAlonzo.RTE.mazUnreachableError) in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                  -> let v14
                                           = let v14
                                                   = case coe v10 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                         -> case coe v14 of
                                                              MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                -> case coe v15 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                       -> coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe v14)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                     _ -> coe v11
                                                              _ -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                    -> case coe v15 of
                                                         MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                           -> case coe v16 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                  -> coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe v15)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                _ -> coe v14
                                                         _ -> coe v14
                                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                                     coe
                                       (if coe v12
                                          then case coe v13 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                   -> case coe v9 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                          -> case coe v16 of
                                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                 -> case coe v17 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                        -> case coe v10 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                               -> case coe v19 of
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                      -> case coe
                                                                                                v20 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased)
                                                                                           _ -> coe
                                                                                                  v14
                                                                                    _ -> coe v14
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v14
                                                               _ -> coe v14
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> coe v14
                                          else (case coe v13 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                    -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  _ -> coe v14))
                                _ -> MAlonzo.RTE.mazUnreachableError))))
             MAlonzo.Code.Once.Type.C_Eff_44 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v4 v5
               -> let v6 = d__'8799'T__786 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__786 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             MAlonzo.Code.Once.Type.C_Fix_46 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v3
               -> let v4 = d__'8799'T__786 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_48
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_50
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_52
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_54
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_TVar_56 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_56 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_46 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_56 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v2))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                               (coe v3)) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_1040 a0 a1 = ()
data T_InferElabResult_1040
  = C_success_1054 MAlonzo.Code.Once.Type.T_Type_32
                   MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 Integer Integer
                   MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_1056 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_1064 a0 a1 a2 = ()
data T_CheckElabResult_1064
  = C_success_1078 MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
                   Integer Integer MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 |
    C_failure_1080 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_1082 = ()
data T_NamedCtx_1082
  = C_mkCtx_1100 Integer
                 [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                 MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_1092 :: T_NamedCtx_1082 -> Integer
d_size_1092 v0
  = case coe v0 of
      C_mkCtx_1100 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_1094 ::
  T_NamedCtx_1082 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_1094 v0
  = case coe v0 of
      C_mkCtx_1100 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_1096 ::
  T_NamedCtx_1082 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_1096 v0
  = case coe v0 of
      C_mkCtx_1100 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_1098 :: T_NamedCtx_1082 -> Integer
d_freshCounter_1098 v0
  = case coe v0 of
      C_mkCtx_1100 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_1102 :: T_NamedCtx_1082
d_emptyCtx_1102
  = coe
      C_mkCtx_1100 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer))
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_1104 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_NamedCtx_1082
d_extendNamedCtx_1104 v0 v1 v2
  = case coe v0 of
      C_mkCtx_1100 v3 v4 v5 v6
        -> coe
             C_mkCtx_1100 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_1118 :: T_NamedCtx_1082 -> T_NamedCtx_1082
d_bumpFresh_1118 v0
  = case coe v0 of
      C_mkCtx_1100 v1 v2 v3 v4
        -> coe
             C_mkCtx_1100 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_1128 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_1128 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.findVarIndex
d_findVarIndex_1134 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findVarIndex_1134 v0 v1
  = case coe v0 of
      C_mkCtx_1100 v2 v3 v4 v5
        -> coe du_go_1154 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_1154 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_go_1154 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_go_1154 v4 v6 v7
du_go_1154 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_go_1154 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v6 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v3))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_1154 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v13)
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.Subst
d_Subst_1226 :: ()
d_Subst_1226 = erased
-- Once.TypeCheck.Elaborate.emptySubst
d_emptySubst_1228 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptySubst_1228
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.extendSubst
d_extendSubst_1230 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendSubst_1230 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.TypeCheck.Elaborate.lookupSubst
d_lookupSubst_1238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_32
d_lookupSubst_1238 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupSubst_1238 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySubst
d_applySubst_1268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32
d_applySubst_1268 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_34 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_36 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__38 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__38
             (coe d_applySubst_1268 (coe v0) (coe v2))
             (coe d_applySubst_1268 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'43'__40 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C__'43'__40
             (coe d_applySubst_1268 (coe v0) (coe v2))
             (coe d_applySubst_1268 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
             (coe d_applySubst_1268 (coe v0) (coe v2)) (coe v3)
             (coe d_applySubst_1268 (coe v0) (coe v4))
      MAlonzo.Code.Once.Type.C_Eff_44 v2 v3
        -> coe
             MAlonzo.Code.Once.Type.C_Eff_44
             (coe d_applySubst_1268 (coe v0) (coe v2))
             (coe d_applySubst_1268 (coe v0) (coe v3))
      MAlonzo.Code.Once.Type.C_Fix_46 v2
        -> coe
             MAlonzo.Code.Once.Type.C_Fix_46
             (coe d_applySubst_1268 (coe v0) (coe v2))
      MAlonzo.Code.Once.Type.C_Int_48 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_50 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_52 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_54 -> coe v1
      MAlonzo.Code.Once.Type.C_TVar_56 v2
        -> let v3 = d_lookupSubst_1238 (coe v0) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4 -> coe v4
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.instantiate
d_instantiate_1330 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate_1330 v0 v1
  = coe du_go_1340 (coe v0) (coe v1) (coe d_emptySubst_1228)
-- Once.TypeCheck.Elaborate._.go
d_go_1340 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1340 ~v0 ~v1 v2 v3 v4 = du_go_1340 v2 v3 v4
du_go_1340 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1340 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Void_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C__'42'__38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1340 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1340 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__'43'__40 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'43'__40
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1340 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1340 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1340 (coe v5)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1340 (coe v5)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_Eff_44 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_Eff_44
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_go_1340 (coe v4)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   du_go_1340 (coe v4)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
                   (coe v2)))
      MAlonzo.Code.Once.Type.C_Fix_46 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Type.C_Fix_46
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe du_go_1340 (coe v3) (coe v1) (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe du_go_1340 (coe v3) (coe v1) (coe v2)))
      MAlonzo.Code.Once.Type.C_Int_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Float_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Str_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_Buffer_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
      MAlonzo.Code.Once.Type.C_TVar_56 v3
        -> let v4 = d_lookupSubst_1238 (coe v2) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v1)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.builtinType
d_builtinType_1472 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinType_1472 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__38
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56
                           (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_fst''_210
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_56
                              (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1))))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_170
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                     (coe addInt (coe (1 :: Integer)) (coe v1))))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__40
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56
                           (coe
                              d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_inl''_230
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56
                        (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1))))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__40
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56
                           (coe
                              d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_inr''_240
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56
                           (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.d__'8658'__64
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_56
                              (coe d_freshTVar_1128 (coe addInt (coe (2 :: Integer)) (coe v1)))))
                        (coe
                           MAlonzo.Code.Once.Type.d__'8658'__64
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__38
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_56
                                 (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_56
                                 (coe
                                    d_freshTVar_1128
                                    (coe addInt (coe (2 :: Integer)) (coe v1))))))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_pair_200
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_190
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_56
                                       (coe d_freshTVar_1128 (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe
                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_190
                                    (coe
                                       MAlonzo.Code.Once.Type.C_TVar_56
                                       (coe d_freshTVar_1128 (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                     (coe addInt (coe (3 :: Integer)) (coe v1))))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.d__'8658'__64
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__38
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56
                           (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_56
                        (coe d_freshTVar_1128 (coe addInt (coe (1 :: Integer)) (coe v1)))))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_180
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_snd''_220
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_56 (coe d_freshTVar_1128 (coe v1)))
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe addInt (coe (2 :: Integer)) (coe v1))))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Type.C_Unit_34)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258) (coe v1)))
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.lookupVar
d_lookupVar_1516 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupVar_1516 v0 v1
  = case coe v0 of
      C_mkCtx_1100 v2 v3 v4 v5
        -> coe du_go_1538 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_1538 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1538 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_go_1538 v4 v5 v6 v7 v8
du_go_1538 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1538 v0 v1 v2 v3 v4
  = case coe v2 of
      []
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> let v5 = d_builtinType_1472 (coe v0) (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     d_weakenFromEmpty_284 (coe (0 :: Integer))
                                                     (coe v3) (coe v7) (coe v9))
                                                  (coe v10)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v6 v7 v8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v8 v9 v10
               -> let v11 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (let v12
                           = let v12
                                   = coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                       erased
                                       (\ v12 ->
                                          coe
                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                            (coe v0))
                                       (coe
                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Context.d_name_14
                                             (coe v5))) in
                             coe
                               (case coe v12 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                    -> if coe v13
                                         then coe
                                                seq (coe v14)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                         (coe v4))))
                                         else coe
                                                seq (coe v14)
                                                (let v15
                                                       = coe
                                                           du_go_1538 (coe v0) (coe v11) (coe v6)
                                                           (coe v8) (coe v4) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                        -> case coe v16 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                               -> case coe v18 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe v17)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Postulates.d_coerceQuantity_168
                                                                                    v11 v8 v9 v17
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                                    v10
                                                                                    (d_weaken_294
                                                                                       (coe v11)
                                                                                       (coe v8)
                                                                                       (coe v9)
                                                                                       (coe v17)
                                                                                       (coe v19)))
                                                                                 (coe v20)))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v15
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Once.Type.C_Many_10
                            -> let v13
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v13 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Context.d_name_14
                                               (coe v5))) in
                               coe
                                 (case coe v13 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                      -> if coe v14
                                           then coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v9)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_170
                                                              (coe
                                                                 MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                                           (coe v4))))
                                           else coe
                                                  seq (coe v15)
                                                  (let v16
                                                         = coe
                                                             du_go_1538 (coe v0) (coe v11) (coe v6)
                                                             (coe v8) (coe v4) in
                                                   coe
                                                     (case coe v16 of
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                          -> case coe v17 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                 -> case coe v19 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                        -> coe
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v18)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      d_weaken_294
                                                                                      (coe v11)
                                                                                      (coe v8)
                                                                                      (coe v9)
                                                                                      (coe v18)
                                                                                      (coe v20))
                                                                                   (coe v21)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                          -> coe v16
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabImpl
d_checkElabImpl_1718 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_CheckElabResult_1064
d_checkElabImpl_1718 v0 v1 v2
  = let v3
          = let v3 = d_inferElabImpl_1722 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_1054 v4 v5 v6 v7 v8
                   -> let v9 = d__'8799'T__786 (coe v4) (coe v2) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe C_success_1078 (coe v5) (coe v6) (coe v7) (coe v8))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            C_failure_1080
                                            (coe
                                               ("Type mismatch in checking mode"
                                                ::
                                                Data.Text.Text)))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_1056 v4 -> coe C_failure_1080 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v4 v5
           -> let v6
                    = coe
                        C_failure_1080
                        (coe ("Lambda requires function type" :: Data.Text.Text)) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Type.C_Zero_6
                            -> coe
                                 C_failure_1080
                                 (coe
                                    ("Erased functions not yet supported in Surface syntax"
                                     ::
                                     Data.Text.Text))
                          MAlonzo.Code.Once.Type.C_One_8
                            -> coe
                                 C_failure_1080
                                 (coe
                                    ("Linear functions not yet supported in Surface syntax"
                                     ::
                                     Data.Text.Text))
                          MAlonzo.Code.Once.Type.C_Many_10
                            -> let v10
                                     = d_checkElabImpl_1718
                                         (coe d_extendNamedCtx_1104 (coe v0) (coe v4) (coe v7))
                                         (coe v5) (coe v9) in
                               coe
                                 (case coe v10 of
                                    C_success_1078 v11 v12 v13 v14
                                      -> coe
                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                           (coe
                                              MAlonzo.Code.Once.Type.d__'8804'q__28
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                                 (coe v14)
                                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                              (coe v8))
                                           (coe
                                              C_success_1078
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v11)
                                              (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                                 (coe v14)))
                                           (coe
                                              C_failure_1080
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("Parameter '" :: Data.Text.Text)
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v4
                                                    (coe
                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                       ("' used with quantity " :: Data.Text.Text)
                                                       (coe
                                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                          (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                                                (coe v14)
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                          (coe
                                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                             (" but declared with quantity "
                                                              ::
                                                              Data.Text.Text)
                                                             (MAlonzo.Code.Once.Type.d_showQuantity_30
                                                                (coe v8))))))))
                                    C_failure_1080 v11 -> coe v10
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabImpl
d_inferElabImpl_1722 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040
d_inferElabImpl_1722 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_1538 (coe v2) (coe d_size_1092 (coe v0))
                     (coe d_named_1094 (coe v0)) (coe d_debruijn_1096 (coe v0))
                     (coe d_freshCounter_1098 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> let v9
                                         = coe
                                             du_go_1154 (coe v2) (coe d_named_1094 (coe v0))
                                             (coe d_debruijn_1096 (coe v0)) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                          -> coe
                                               C_success_1054 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                  (coe d_size_1092 (coe v0)) (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.du_lookupQuantity_38
                                                     (coe d_debruijn_1096 (coe v0)) (coe v10)))
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> coe
                                               C_success_1054 (coe v5) (coe v7) (coe (0 :: Integer))
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_1092 (coe v0)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_1056
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v2 v3
        -> coe
             du_inferApp_1952 (coe v0) (coe v3)
             (coe d_inferElabImpl_1722 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v2 v3
        -> let v4
                 = d_inferElabImpl_1722
                     (coe
                        d_extendNamedCtx_1104 (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_56 (coe ("\945" :: Data.Text.Text))))
                     (coe v3) in
           coe
             (case coe v4 of
                C_success_1054 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Once.Type.d__'8804'q__28
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140 (coe v9)
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          C_success_1054
                          (coe
                             MAlonzo.Code.Once.Type.d__'8658'__64
                             (coe
                                MAlonzo.Code.Once.Type.C_TVar_56 (coe ("\945" :: Data.Text.Text)))
                             (coe v5))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_180 v6)
                          (coe addInt (coe (1 :: Integer)) (coe v7)) (coe v8)
                          (coe MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154 (coe v9)))
                       (coe
                          C_failure_1056
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("Lambda parameter '" :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("' used with quantity " :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                      (MAlonzo.Code.Once.Type.d_showQuantity_30
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.du_lookupUsage_140
                                            (coe v9) (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                      (coe
                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                         (" but inferred lambdas require \8804 " :: Data.Text.Text)
                                         (MAlonzo.Code.Once.Type.d_showQuantity_30
                                            (coe MAlonzo.Code.Once.Type.C_Many_10))))))))
                C_failure_1056 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v2 v3 v4
        -> let v5 = d_inferElabImpl_1722 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_1054 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElabImpl_1722
                               (coe du_extendNamedCtx''_2162 (coe v0) (coe v2) (coe v6) (coe v9))
                               (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_1054 v12 v13 v14 v15 v16
                            -> coe
                                 C_success_1054 (coe v12)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_let''_276 v6 v7 v13)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8)
                                    (coe addInt (coe (1 :: Integer)) (coe v14)))
                                 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154 (coe v16)))
                          C_failure_1056 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_1056 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v2 v3
        -> let v4 = d_inferElabImpl_1722 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_1054 v5 v6 v7 v8 v9
                  -> let v10
                           = d_inferElabImpl_1722
                               (coe du_bumpFresh''_2058 (coe v0) (coe v8)) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_1054 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_1054
                                 (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v11))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_200 v6 v12)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v13))
                                 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v9)
                                    (coe v15))
                          C_failure_1056 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_1056 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RCase_46 v2 v3 v4 v5 v6
        -> coe
             du_inferCase_2258 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_inferElabImpl_1722 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48
        -> coe
             C_success_1054 (coe MAlonzo.Code.Once.Type.C_Unit_34)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_258)
             (coe (0 :: Integer)) (coe d_freshCounter_1098 (coe v0))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_1092 (coe v0)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v2
        -> coe
             C_failure_1056
             (coe
                ("Integer literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v2
        -> coe
             C_failure_1056
             (coe
                ("String literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v2 v3
        -> coe d_inferElabImpl_1722 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v2 v3 v4
        -> coe
             C_failure_1056
             (coe
                ("Binary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v3
        -> coe
             C_failure_1056
             (coe
                ("Unary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferApp
d_inferApp_1952 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
d_inferApp_1952 v0 ~v1 v2 v3 = du_inferApp_1952 v0 v2 v3
du_inferApp_1952 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
du_inferApp_1952 v0 v1 v2
  = case coe v2 of
      C_success_1054 v3 v4 v5 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__38 v8 v9
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v8 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           C_failure_1056
                           (coe
                              ("Erased functions not yet supported in Surface syntax"
                               ::
                               Data.Text.Text))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           C_failure_1056
                           (coe
                              ("Linear functions not yet supported in Surface syntax"
                               ::
                               Data.Text.Text))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           du_inferArg_1982 (coe v8) (coe v10) (coe v4) (coe v5) (coe v7)
                           (coe
                              d_inferElabImpl_1722 (coe du_bumpFreshTo_1972 (coe v0) (coe v6))
                              (coe v1))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_Eff_44 v8 v9
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_46 v8
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_56 v8
               -> coe
                    C_failure_1056
                    (coe ("Expected function type in application" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_1056 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.bumpFreshTo
d_bumpFreshTo_1972 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_NamedCtx_1082 -> Integer -> T_NamedCtx_1082
d_bumpFreshTo_1972 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bumpFreshTo_1972 v9 v10
du_bumpFreshTo_1972 ::
  T_NamedCtx_1082 -> Integer -> T_NamedCtx_1082
du_bumpFreshTo_1972 v0 v1
  = case coe v0 of
      C_mkCtx_1100 v2 v3 v4 v5
        -> coe C_mkCtx_1100 (coe v2) (coe v3) (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArg
d_inferArg_1982 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
d_inferArg_1982 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 v8 v9
  = du_inferArg_1982 v3 v4 v5 v6 v8 v9
du_inferArg_1982 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
du_inferArg_1982 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_1054 v6 v7 v8 v9 v10
        -> let v11 = d__'8799'T__786 (coe v0) (coe v6) in
           coe
             (case coe v11 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                  -> if coe v12
                       then coe
                              seq (coe v13)
                              (coe
                                 C_success_1054 (coe v1)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_app_190 v6 v2 v7)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v8))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v4)
                                    (coe v10)))
                       else coe
                              seq (coe v13)
                              (coe
                                 C_failure_1056
                                 (coe ("Type mismatch in application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_1056 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.bumpFresh'
d_bumpFresh''_2058 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_1082 -> Integer -> T_NamedCtx_1082
d_bumpFresh''_2058 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_bumpFresh''_2058 v8 v9
du_bumpFresh''_2058 ::
  T_NamedCtx_1082 -> Integer -> T_NamedCtx_1082
du_bumpFresh''_2058 v0 v1
  = case coe v0 of
      C_mkCtx_1100 v2 v3 v4 v5
        -> coe C_mkCtx_1100 (coe v2) (coe v3) (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendNamedCtx'
d_extendNamedCtx''_2162 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer -> T_NamedCtx_1082
d_extendNamedCtx''_2162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                        v11 v12
  = du_extendNamedCtx''_2162 v9 v10 v11 v12
du_extendNamedCtx''_2162 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer -> T_NamedCtx_1082
du_extendNamedCtx''_2162 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_1100 v4 v5 v6 v7
        -> coe
             C_mkCtx_1100 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.extendCtx'
d_extendCtx''_2244 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer -> T_NamedCtx_1082
d_extendCtx''_2244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_extendCtx''_2244 v6 v7 v8 v9
du_extendCtx''_2244 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> Integer -> T_NamedCtx_1082
du_extendCtx''_2244 v0 v1 v2 v3
  = case coe v0 of
      C_mkCtx_1100 v4 v5 v6 v7
        -> coe
             C_mkCtx_1100 (coe addInt (coe (1 :: Integer)) (coe v4))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v5)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v6) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferCase
d_inferCase_2258 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
d_inferCase_2258 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferCase_2258 v0 v2 v3 v4 v5 v6
du_inferCase_2258 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
du_inferCase_2258 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_1054 v6 v7 v8 v9 v10
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_Unit_34
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_36
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__38 v11 v12
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__40 v11 v12
               -> coe
                    du_inferLeft_2278 (coe v0) (coe v3) (coe v4) (coe v11) (coe v12)
                    (coe v7) (coe v8) (coe v10)
                    (coe
                       d_inferElabImpl_1722
                       (coe du_extendCtx''_2244 (coe v0) (coe v1) (coe v11) (coe v9))
                       (coe v2))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v11 v12 v13
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Eff_44 v11 v12
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_46 v11
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_48
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_50
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_52
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_54
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_56 v11
               -> coe
                    C_failure_1056
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_1056 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferLeft
d_inferLeft_2278 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
d_inferLeft_2278 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_inferLeft_2278 v0 v4 v5 v6 v7 v8 v9 v11 v12
du_inferLeft_2278 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
du_inferLeft_2278 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      C_success_1054 v9 v10 v11 v12 v13
        -> coe
             du_inferRight_2296 (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
             (coe v9) (coe v10) (coe v11) (coe v13)
             (coe
                d_inferElabImpl_1722
                (coe du_extendCtx''_2244 (coe v0) (coe v1) (coe v4) (coe v12))
                (coe v2))
      C_failure_1056 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.inferRight
d_inferRight_2296 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
d_inferRight_2296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                  v13 v14 ~v15 v16 v17
  = du_inferRight_2296 v6 v7 v8 v9 v11 v12 v13 v14 v16 v17
du_inferRight_2296 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  T_InferElabResult_1040 -> T_InferElabResult_1040
du_inferRight_2296 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_success_1054 v10 v11 v12 v13 v14
        -> let v15 = d__'8799'T__786 (coe v5) (coe v10) in
           coe
             (case coe v15 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                  -> if coe v16
                       then coe
                              seq (coe v17)
                              (coe
                                 C_success_1054 (coe v10)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_case''_252 v0 v1 v2 v6 v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                       (coe addInt (coe (1 :: Integer)) (coe v7)))
                                    (coe addInt (coe (1 :: Integer)) (coe v12)))
                                 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                          (coe v8)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du_tailUsage_154
                                       (coe v14))))
                       else coe
                              seq (coe v17)
                              (coe
                                 C_failure_1056
                                 (coe ("Case branches have different types" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_1056 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_2340 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_1040
d_inferElab_2340 v0 v1
  = let v2 = d_inferElabImpl_1722 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_1054 v3 v4 v5 v6 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v8 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v5))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v5)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                     -> if coe v9
                          then coe seq (coe v10) (coe v2)
                          else coe
                                 seq (coe v10)
                                 (coe
                                    C_failure_1056
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("Expression nesting depth exceeds verified limit.\n"
                                        ::
                                        Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("  Depth encountered: " :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("\n" :: Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("  Proven depth limit: 7\n" :: Data.Text.Text)
                                                   ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                    ::
                                                    Data.Text.Text)))))))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1056 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_2406 ::
  T_NamedCtx_1082 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> T_CheckElabResult_1064
d_checkElab_2406 v0 v1 v2
  = let v3 = d_checkElabImpl_1718 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         C_success_1078 v4 v5 v6 v7
           -> let v8
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v8 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v5))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v5)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                     -> if coe v9
                          then coe seq (coe v10) (coe v3)
                          else coe
                                 seq (coe v10)
                                 (coe
                                    C_failure_1080
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("Expression nesting depth exceeds verified limit.\n"
                                        ::
                                        Data.Text.Text)
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("  Depth encountered: " :: Data.Text.Text)
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v5)
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("\n" :: Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("  Proven depth limit: 7\n" :: Data.Text.Text)
                                                   ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                    ::
                                                    Data.Text.Text)))))))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1080 v4 -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_2474 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_4
d_compileExprTyped_2474 v0 v1
  = let v2
          = d_checkElabImpl_1718 (coe d_emptyCtx_1102) (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_1078 v3 v4 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v4))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v4)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then let v10 = seq (coe v9) (coe v2) in
                               coe
                                 (case coe v10 of
                                    C_success_1078 v11 v12 v13 v14
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                              (coe v1) (coe v11))
                                    C_failure_1080 v11
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v10
                                      = seq
                                          (coe v9)
                                          (coe
                                             C_failure_1080
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("Expression nesting depth exceeds verified limit.\n"
                                                 ::
                                                 Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("  Depth encountered: " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         ("\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v10 of
                                     C_success_1078 v11 v12 v13 v14
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                                               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                               (coe v1) (coe v11))
                                     C_failure_1080 v11
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1080 v3
           -> case coe v2 of
                C_success_1078 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                          (coe v4))
                C_failure_1080 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_2496 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_2496 v0
  = let v1 = d_inferElabImpl_1722 (coe d_emptyCtx_1102) (coe v0) in
    coe
      (case coe v1 of
         C_success_1054 v2 v3 v4 v5 v6
           -> let v7
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                             (coe v4))
                        (coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                        (coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                           (coe
                              MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v4)
                              (coe (7 :: Integer)))) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then let v10 = seq (coe v9) (coe v1) in
                               coe
                                 (case coe v10 of
                                    C_success_1054 v11 v12 v13 v14 v15
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                 (coe v11) (coe v12)))
                                    C_failure_1056 v11
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v10
                                      = seq
                                          (coe v9)
                                          (coe
                                             C_failure_1056
                                             (coe
                                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                ("Expression nesting depth exceeds verified limit.\n"
                                                 ::
                                                 Data.Text.Text)
                                                (coe
                                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                   ("  Depth encountered: " :: Data.Text.Text)
                                                   (coe
                                                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v4)
                                                      (coe
                                                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                         ("\n" :: Data.Text.Text)
                                                         (coe
                                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v10 of
                                     C_success_1054 v11 v12 v13 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                  (coe v11) (coe v12)))
                                     C_failure_1056 v11
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1056 v2
           -> case coe v1 of
                C_success_1054 v3 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_76
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v3)
                             (coe v4)))
                C_failure_1056 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
