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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
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
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc_14 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc
d_lookup'45'suc'45'suc_36 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc_36 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc_58 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc_84 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc_84 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc_114 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_148 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_148 = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_186 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_186
  = erased
-- Once.TypeCheck.Elaborate.lookup-suc-suc-suc-suc-suc-suc-suc-suc
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_228 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc'45'suc_228
  = erased
-- Once.TypeCheck.Elaborate.exchange₈
d_exchange'8328'_274
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.exchange\8328"
-- Once.TypeCheck.Elaborate.weakenFromEmpty
d_weakenFromEmpty_282 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_weakenFromEmpty_282 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8 -> coe v3
      MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v5 v6
        -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_weaken_292 (coe v7) (coe v5) (coe v6) (coe v2)
                (coe d_weakenFromEmpty_282 (coe v7) (coe v5) (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.weaken
d_weaken_292 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_weaken_292 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v7
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_var_36
             (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v7)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange_304
                       (coe v0) (coe v1) (coe v2) (coe v10) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v7
             (d_weaken_292
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v7) (coe v3))
                (coe v9))
             (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v7) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v9 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__10 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                    (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v8 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v8
             (d_weaken_292
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v3) (coe v8))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v7 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v7
             (d_weaken_292
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v7) (coe v3))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__12 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v10) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__12 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v7 v8
             (d_weaken_292
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v7) (coe v8))
                (coe v10))
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v11))
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v3) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_weaken_292
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Once.Type.C_Void_8)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v7
             (d_weaken_292 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9))
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange
d_exchange_304 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange_304 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v8
        -> case coe v8 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v10
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe
                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                       (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8322'_318
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v8
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v8) (coe v4))
                (coe v10))
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v10 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'42'__10 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange_304
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
                    (d_exchange_304
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v9
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v4) (coe v9))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v8 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v8
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v4))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__12 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange_304
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__12 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange_304
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v8 v9
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v8) (coe v9))
                (coe v11))
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v12))
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v4) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v8
             (d_exchange_304
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v10))
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₂
d_exchange'8322'_318 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8322'_318 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v9
        -> case coe v9 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v11
               -> case coe v11 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v13
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe
                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8323'_334
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v9
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v9) (coe v5))
                (coe v11))
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__10 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8322'_318
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
                    (d_exchange'8322'_318
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v14) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v10
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v10))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v9 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v9
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v9) (coe v5))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8322'_318
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8322'_318
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v9 v10 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v9 v10
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v9) (coe v10))
                (coe v12))
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v13))
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10) (coe v5)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v9
             (d_exchange'8322'_318
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v11))
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₃
d_exchange'8323'_334 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8323'_334 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v10
        -> case coe v10 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v12
               -> case coe v12 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v14
                      -> case coe v14 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8324'_352
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v14) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v10
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v10) (coe v6))
                (coe v12))
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'42'__10 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8323'_334
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
                    (d_exchange'8323'_334
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v15)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v11
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v6) (coe v11))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v10
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v10) (coe v6))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8323'_334
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8323'_334
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v10 v11
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v10) (coe v11))
                (coe v13))
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v14))
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v11)
                (coe v6) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v10
             (d_exchange'8323'_334
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v12))
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v13))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₄
d_exchange'8324'_352 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8324'_352 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v11
        -> case coe v11 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v13
               -> case coe v13 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
                      -> case coe v15 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v17
                             -> case coe v17 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                         (coe
                                            MAlonzo.Code.Data.Fin.Base.C_suc_16
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe
                                                  MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v19
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8325'_372
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v15) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v11
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v11) (coe v7))
                (coe v13))
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v13 v14
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'42'__10 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8324'_352
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
                    (d_exchange'8324'_352
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v12
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v7) (coe v12))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v11 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v11
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v11) (coe v7))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__12 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8324'_352
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__12 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8324'_352
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v11 v12
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v11) (coe v12))
                (coe v14))
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v15))
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v12) (coe v7) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v11
             (d_exchange'8324'_352
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v13))
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v14))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₅
d_exchange'8325'_372 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8325'_372 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v12
        -> case coe v12 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v14
               -> case coe v14 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
                      -> case coe v16 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v18
                             -> case coe v18 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8326'_394
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v15) (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v12
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v12) (coe v8))
                (coe v14))
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v14 v15
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'42'__10 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8325'_372
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
                    (d_exchange'8325'_372
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v13
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v13))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v12 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v12
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v12) (coe v8))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8325'_372
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v15) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8325'_372
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v12 v13
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v12) (coe v13))
                (coe v15))
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v8) (coe v16))
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v13) (coe v8) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v12
             (d_exchange'8325'_372
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v14))
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v8) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₆
d_exchange'8326'_394 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8326'_394 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v13
        -> case coe v13 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
               -> case coe v15 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v19
                             -> case coe v19 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (d_exchange'8327'_418
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v16) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v13
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v13) (coe v9))
                (coe v15))
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v15 v16
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'42'__10 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8326'_394
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v17) (coe v15))
                    (d_exchange'8326'_394
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v18) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v14
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v9) (coe v14))
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v13 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v13
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v13) (coe v9))
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'43'__12 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8326'_394
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v15
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'43'__12 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8326'_394
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v13 v14
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v13) (coe v14))
                (coe v16))
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v9) (coe v17))
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v14) (coe v9) (coe v18))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v13 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v13
             (d_exchange'8326'_394
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v15))
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v13) (coe v9) (coe v16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₇
d_exchange'8327'_418 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8327'_418 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_36 v14
        -> case coe v14 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
               -> case coe v16 of
                    MAlonzo.Code.Data.Fin.Base.C_zero_12
                      -> coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                    MAlonzo.Code.Data.Fin.Base.C_suc_16 v18
                      -> case coe v18 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12
                             -> coe
                                  MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                  (coe
                                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                                     (coe
                                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v20
                             -> case coe v20 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12
                                    -> coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                       MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
                                                              MAlonzo.Code.Once.Surface.Syntax.C_var_36
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
      MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'8658'__14 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                    (coe
                       d_exchange'8328'_274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v17 v18 v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v14
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v14) (coe v10))
                (coe v16))
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v14) (coe v17))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v16 v17
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'42'__10 v18 v19
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8327'_418
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v18) (coe v16))
                    (d_exchange'8327'_418
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v19) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v15
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v10) (coe v15))
                (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v14 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v14
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v14) (coe v10))
                (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'43'__12 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8327'_418
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v17) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v16
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C__'43'__12 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8327'_418
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v9) (coe v18) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v14 v15
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v14) (coe v15))
                (coe v17))
             (coe
                d_exchange'8328'_274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v14 v10 v18)
             (coe
                d_exchange'8328'_274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v15 v10 v19)
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe MAlonzo.Code.Once.Type.C_Void_8)
                (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v14
             (d_exchange'8327'_418
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe v9) (coe v14) (coe v16))
             (coe
                d_exchange'8328'_274 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v14 v10 v17)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__776 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__776 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> let v6 = d__'8799'T__776 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__776 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> let v6 = d__'8799'T__776 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__776 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> let v6 = d__'8799'T__776 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__776 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v4 v5
               -> let v6 = d__'8799'T__776 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__776 (coe v3) (coe v5) in
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
             MAlonzo.Code.Once.Type.C_Fix_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Fix_18 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v3
               -> let v4 = d__'8799'T__776 (coe v2) (coe v3) in
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
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_20
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_22
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_24
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_26
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_TVar_28 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_TVar_28 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__10 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__12 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658'__14 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Eff_16 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Fix_18 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_TVar_28 v3
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
d_InferElabResult_998 a0 a1 = ()
data T_InferElabResult_998
  = C_success_1008 MAlonzo.Code.Once.Type.T_Type_4
                   MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 Integer |
    C_failure_1010 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_1012 = ()
data T_NamedCtx_1012
  = C_mkCtx_1026 Integer
                 [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14]
                 MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_1020 :: T_NamedCtx_1012 -> Integer
d_size_1020 v0
  = case coe v0 of
      C_mkCtx_1026 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_1022 ::
  T_NamedCtx_1012 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14]
d_named_1022 v0
  = case coe v0 of
      C_mkCtx_1026 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_1024 ::
  T_NamedCtx_1012 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_1024 v0
  = case coe v0 of
      C_mkCtx_1026 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_1028 :: T_NamedCtx_1012
d_emptyCtx_1028
  = coe
      C_mkCtx_1026 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_32)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_1030 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> T_NamedCtx_1012
d_extendNamedCtx_1030 v0 v1 v2
  = case coe v0 of
      C_mkCtx_1026 v3 v4 v5
        -> coe
             C_mkCtx_1026 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__34 (coe v4)
                (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v5 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.builtinType
d_builtinType_1044 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_builtinType_1044 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__10
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_fst''_76
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         l | (==) l ("id" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_var_36
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__12
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text)))
                     (coe
                        MAlonzo.Code.Once.Type.C__'43'__12
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658'__14
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text))))
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658'__14
                        (coe
                           MAlonzo.Code.Once.Type.C__'8658'__14
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_28 (coe ("c" :: Data.Text.Text))))
                        (coe
                           MAlonzo.Code.Once.Type.C__'8658'__14
                           (coe
                              MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__10
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text)))
                              (coe
                                 MAlonzo.Code.Once.Type.C_TVar_28 (coe ("c" :: Data.Text.Text)))))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_app_56
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe
                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_app_56
                                 (coe
                                    MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                    (coe
                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))))
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658'__14
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__10
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text))))
                     (coe
                        MAlonzo.Code.Once.Type.C_TVar_28 (coe ("b" :: Data.Text.Text))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_lam_46
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C_snd''_86
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("a" :: Data.Text.Text)))
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C_var_36
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Type.C_Unit_6)
                  (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124))
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.lookupVar
d_lookupVar_1050 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupVar_1050 v0 v1
  = case coe v0 of
      C_mkCtx_1026 v2 v3 v4
        -> coe du_go_1070 (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_1070 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_1070 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_go_1070 v3 v4 v5 v6
du_go_1070 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1070 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> let v4 = d_builtinType_1044 (coe v0) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                        (coe
                                           d_weakenFromEmpty_282 (coe (0 :: Integer)) (coe v3)
                                           (coe v6) (coe v7)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v7 v8
               -> let v9 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (let v10
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v10 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v0))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_22 (coe v4))) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.C_var_36
                                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                 else coe
                                        seq (coe v12)
                                        (let v13
                                               = coe
                                                   du_go_1070 (coe v0) (coe v9) (coe v5) (coe v7) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                -> case coe v14 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v15)
                                                               (coe
                                                                  d_weaken_292 (coe v9) (coe v7)
                                                                  (coe v8) (coe v15) (coe v16)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v13
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabImpl
d_inferElabImpl_1144 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998
d_inferElabImpl_1144 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_1070 (coe v2) (coe d_size_1020 (coe v0))
                     (coe d_named_1022 (coe v0)) (coe d_debruijn_1024 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe C_success_1008 (coe v5) (coe v6) (coe (0 :: Integer))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_1010
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v2 v3
        -> coe
             du_inferApp_1206 (coe v0) (coe v3)
             (coe d_inferElabImpl_1144 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v2 v3
        -> let v4
                 = d_inferElabImpl_1144
                     (coe
                        d_extendNamedCtx_1030 (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("\945" :: Data.Text.Text))))
                     (coe v3) in
           coe
             (case coe v4 of
                C_success_1008 v5 v6 v7
                  -> coe
                       C_success_1008
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658'__14
                          (coe
                             MAlonzo.Code.Once.Type.C_TVar_28 (coe ("\945" :: Data.Text.Text)))
                          (coe v5))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v6)
                       (coe addInt (coe (1 :: Integer)) (coe v7))
                C_failure_1010 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v2 v3 v4
        -> let v5 = d_inferElabImpl_1144 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_1008 v6 v7 v8
                  -> let v9
                           = d_inferElabImpl_1144
                               (coe d_extendNamedCtx_1030 (coe v0) (coe v2) (coe v6)) (coe v4) in
                     coe
                       (case coe v9 of
                          C_success_1008 v10 v11 v12
                            -> coe
                                 C_success_1008 (coe v10)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v6 v7 v11)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8)
                                    (coe addInt (coe (1 :: Integer)) (coe v12)))
                          C_failure_1010 v10 -> coe v9
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_1010 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v2 v3
        -> let v4 = d_inferElabImpl_1144 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_1008 v5 v6 v7
                  -> let v8 = d_inferElabImpl_1144 (coe v0) (coe v3) in
                     coe
                       (case coe v8 of
                          C_success_1008 v9 v10 v11
                            -> coe
                                 C_success_1008
                                 (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v9))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v6 v10)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7) (coe v11))
                          C_failure_1010 v9 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_1010 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RCase_46 v2 v3 v4 v5 v6
        -> coe
             du_inferCase_1408 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_inferElabImpl_1144 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48
        -> coe
             C_success_1008 (coe MAlonzo.Code.Once.Type.C_Unit_6)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124)
             (coe (0 :: Integer))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v2
        -> coe
             C_failure_1010
             (coe
                ("Integer literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v2
        -> coe
             C_failure_1010
             (coe
                ("String literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v2 v3
        -> coe d_inferElabImpl_1144 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v2 v3 v4
        -> coe
             C_failure_1010
             (coe
                ("Binary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v3
        -> coe
             C_failure_1010
             (coe
                ("Unary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferApp
d_inferApp_1206 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998 -> T_InferElabResult_998
d_inferApp_1206 v0 ~v1 v2 v3 = du_inferApp_1206 v0 v2 v3
du_inferApp_1206 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998 -> T_InferElabResult_998
du_inferApp_1206 v0 v1 v2
  = case coe v2 of
      C_success_1008 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__10 v6 v7
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__12 v6 v7
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'8658'__14 v6 v7
               -> coe
                    du_inferArg_1222 (coe v6) (coe v7) (coe v4) (coe v5)
                    (coe d_inferElabImpl_1144 (coe v0) (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_16 v6 v7
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_18 v6
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_28 v6
               -> coe
                    C_failure_1010
                    (coe ("Expected function type in application" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_1010 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArg
d_inferArg_1222 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
d_inferArg_1222 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_inferArg_1222 v3 v4 v5 v6 v7
du_inferArg_1222 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
du_inferArg_1222 v0 v1 v2 v3 v4
  = case coe v4 of
      C_success_1008 v5 v6 v7
        -> let v8 = d__'8799'T__776 (coe v0) (coe v5) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe
                              seq (coe v10)
                              (coe
                                 C_success_1008 (coe v1)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_app_56 v5 v2 v6)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v7)))
                       else coe
                              seq (coe v10)
                              (coe
                                 C_failure_1010
                                 (coe ("Type mismatch in application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_1010 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferCase
d_inferCase_1408 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998 -> T_InferElabResult_998
d_inferCase_1408 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferCase_1408 v0 v2 v3 v4 v5 v6
du_inferCase_1408 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998 -> T_InferElabResult_998
du_inferCase_1408 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_1008 v6 v7 v8
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__10 v9 v10
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__12 v9 v10
               -> coe
                    du_inferLeft_1424 (coe v0) (coe v3) (coe v4) (coe v9) (coe v10)
                    (coe v7) (coe v8)
                    (coe
                       d_inferElabImpl_1144
                       (coe d_extendNamedCtx_1030 (coe v0) (coe v1) (coe v9)) (coe v2))
             MAlonzo.Code.Once.Type.C__'8658'__14 v9 v10
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Eff_16 v9 v10
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_18 v9
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_28 v9
               -> coe
                    C_failure_1010
                    (coe ("Expected sum type in case" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_1010 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferLeft
d_inferLeft_1424 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
d_inferLeft_1424 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_inferLeft_1424 v0 v4 v5 v6 v7 v8 v9 v10
du_inferLeft_1424 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
du_inferLeft_1424 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_1008 v8 v9 v10
        -> coe
             du_inferRight_1438 (coe v3) (coe v4) (coe v5) (coe v6) (coe v8)
             (coe v9) (coe v10)
             (coe
                d_inferElabImpl_1144
                (coe d_extendNamedCtx_1030 (coe v0) (coe v1) (coe v4)) (coe v2))
      C_failure_1010 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.inferRight
d_inferRight_1438 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
d_inferRight_1438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                  v13
  = du_inferRight_1438 v6 v7 v8 v9 v10 v11 v12 v13
du_inferRight_1438 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  Integer -> T_InferElabResult_998 -> T_InferElabResult_998
du_inferRight_1438 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_1008 v8 v9 v10
        -> let v11 = d__'8799'T__776 (coe v4) (coe v8) in
           coe
             (case coe v11 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                  -> if coe v12
                       then coe
                              seq (coe v13)
                              (coe
                                 C_success_1008 (coe v8)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v0 v1 v2 v5 v9)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                       (coe addInt (coe (1 :: Integer)) (coe v6)))
                                    (coe addInt (coe (1 :: Integer)) (coe v10))))
                       else coe
                              seq (coe v13)
                              (coe
                                 C_failure_1010
                                 (coe ("Case branches have different types" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_1010 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1470 ::
  T_NamedCtx_1012 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_998
d_inferElab_1470 v0 v1
  = let v2 = d_inferElabImpl_1144 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_1008 v3 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v6 ->
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
                (case coe v6 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                     -> if coe v7
                          then coe seq (coe v8) (coe v2)
                          else coe
                                 seq (coe v8)
                                 (coe
                                    C_failure_1010
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
         C_failure_1010 v3 -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_1522 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_1522 v0
  = let v1 = d_inferElabImpl_1144 (coe d_emptyCtx_1028) (coe v0) in
    coe
      (case coe v1 of
         C_success_1008 v2 v3 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v5 ->
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
                (case coe v5 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                     -> if coe v6
                          then let v8 = seq (coe v7) (coe v1) in
                               coe
                                 (case coe v8 of
                                    C_success_1008 v9 v10 v11
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                 (coe v9) (coe v10)))
                                    C_failure_1010 v9
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v8
                                      = seq
                                          (coe v7)
                                          (coe
                                             C_failure_1010
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
                                  (case coe v8 of
                                     C_success_1008 v9 v10 v11
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                                  (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                  (coe v9) (coe v10)))
                                     C_failure_1010 v9
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1010 v2
           -> case coe v1 of
                C_success_1008 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v3)
                             (coe v4)))
                C_failure_1010 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_1540 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_4
d_compileExprTyped_1540 v0 v1
  = let v2 = d_inferElabImpl_1144 (coe d_emptyCtx_1028) (coe v0) in
    coe
      (case coe v2 of
         C_success_1008 v3 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        (\ v6 ->
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
                (case coe v6 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                     -> if coe v7
                          then let v9 = seq (coe v8) (coe v2) in
                               coe
                                 (case coe v9 of
                                    C_success_1008 v10 v11 v12
                                      -> let v13 = d__'8799'T__776 (coe v1) (coe v10) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                  (coe v10) (coe v11)))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_1010 v10
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else (let v9
                                      = seq
                                          (coe v8)
                                          (coe
                                             C_failure_1010
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
                                                            ("  Proven depth limit: 7\n"
                                                             ::
                                                             Data.Text.Text)
                                                            ("  Please refactor to reduce nesting of \955/case/let expressions."
                                                             ::
                                                             Data.Text.Text))))))) in
                                coe
                                  (case coe v9 of
                                     C_success_1008 v10 v11 v12
                                       -> let v13 = d__'8799'T__776 (coe v1) (coe v10) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                   (coe v10) (coe v11)))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_1010 v10
                                       -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_1010 v3
           -> case coe v2 of
                C_success_1008 v4 v5 v6
                  -> let v7 = d__'8799'T__776 (coe v1) (coe v4) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                            -> if coe v8
                                 then coe
                                        seq (coe v9)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                              (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                              (coe v4) (coe v5)))
                                 else coe
                                        seq (coe v9)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_1010 v4
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
