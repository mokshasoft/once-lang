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
-- Once.TypeCheck.Elaborate.weaken
d_weaken_174 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_weaken_174 v0 v1 v2 v3 v4
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
                    (d_exchange_186
                       (coe v0) (coe v1) (coe v2) (coe v10) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v7
             (d_weaken_174
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v7) (coe v3))
                (coe v9))
             (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v7) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v9 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__10 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                    (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v8 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v8
             (d_weaken_174
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v3) (coe v8))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v7 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v7
             (d_weaken_174
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v7) (coe v3))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__12 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v10) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v9
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__12 v10 v11
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v7 v8
             (d_weaken_174
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v7) (coe v8))
                (coe v10))
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v11))
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v3) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v8
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_weaken_174
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Once.Type.C_Void_8)
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v7
             (d_weaken_174 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9))
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v7) (coe v3) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange
d_exchange_186 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange_186 v0 v1 v2 v3 v4 v5
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
                    (d_exchange'8322'_200
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v8
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v8) (coe v4))
                (coe v10))
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v10 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'42'__10 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange_186
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
                    (d_exchange_186
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v9 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v9
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v4) (coe v9))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v8 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v8
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v4))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__12 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange_186
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v10
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C__'43'__12 v11 v12
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange_186
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v8 v9
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v8) (coe v9))
                (coe v11))
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v12))
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v9) (coe v4) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v9
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v8
             (d_exchange_186
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v10))
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4) (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₂
d_exchange'8322'_200 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8322'_200 v0 v1 v2 v3 v4 v5 v6
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
                    (d_exchange'8323'_216
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v9
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v9) (coe v5))
                (coe v11))
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v11 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__10 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8322'_200
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
                    (d_exchange'8322'_200
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v14) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v10
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v10))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v9 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v9
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v9) (coe v5))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8322'_200
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v12) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'43'__12 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8322'_200
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v13) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v9 v10 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v9 v10
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v9) (coe v10))
                (coe v12))
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v13))
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10) (coe v5)
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v9
             (d_exchange'8322'_200
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v11))
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v9) (coe v5)
                (coe v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₃
d_exchange'8323'_216 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28
d_exchange'8323'_216 v0 v1 v2 v3 v4 v5 v6 v7
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
                    (d_exchange'8324'_234
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v14) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v10
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v10) (coe v6))
                (coe v12))
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v12 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'42'__10 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8323'_216
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
                    (d_exchange'8323'_216
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v15)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v11
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v6) (coe v11))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v10
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v10) (coe v6))
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8323'_216
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v13)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v12
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C__'43'__12 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8323'_216
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v14)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v10 v11
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v10) (coe v11))
                (coe v13))
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v14))
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v11)
                (coe v6) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v10
             (d_exchange'8323'_216
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v12))
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v10)
                (coe v6) (coe v13))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₄
d_exchange'8324'_234 ::
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
d_exchange'8324'_234 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                    (d_exchange'8325'_254
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v15) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v11
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v11) (coe v7))
                (coe v13))
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v13 v14
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'42'__10 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8324'_234
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
                    (d_exchange'8324'_234
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v12 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v12
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v7) (coe v12))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v11 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v11
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v11) (coe v7))
                (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__12 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8324'_234
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v14) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v13
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__12 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8324'_234
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v15) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v11 v12
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v11) (coe v12))
                (coe v14))
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v15))
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v12) (coe v7) (coe v16))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v11 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v11
             (d_exchange'8324'_234
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v13))
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v11) (coe v7) (coe v14))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₅
d_exchange'8325'_254 ::
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
d_exchange'8325'_254 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
                    (coe d_exchange'8326'_276 v0 v1 v2 v3 v4 v5 v6 v7 v15 v16 v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_56 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_56 v12
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'8658'__14 (coe v12) (coe v8))
                (coe v14))
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v14 v15
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'42'__10 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_66
                    (d_exchange'8325'_254
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
                    (d_exchange'8325'_254
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v17) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v13 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_76 v13
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v8) (coe v13))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v12 v14
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_86 v12
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v12) (coe v8))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_96 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_96
                    (d_exchange'8325'_254
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v15) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_106 v14
        -> case coe v8 of
             MAlonzo.Code.Once.Type.C__'43'__12 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_106
                    (d_exchange'8325'_254
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v16) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v12 v13
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7)
                (coe MAlonzo.Code.Once.Type.C__'43'__12 (coe v12) (coe v13))
                (coe v15))
             (coe d_exchange'8326'_276 v0 v1 v2 v3 v4 v5 v6 v7 v12 v8 v16)
             (coe d_exchange'8326'_276 v0 v1 v2 v3 v4 v5 v6 v7 v13 v8 v17)
      MAlonzo.Code.Once.Surface.Syntax.C_unit_124
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_132 v13
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_132
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe MAlonzo.Code.Once.Type.C_Void_8) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v12
             (d_exchange'8325'_254
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v12) (coe v14))
             (coe d_exchange'8326'_276 v0 v1 v2 v3 v4 v5 v6 v7 v12 v8 v15)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.exchange₆
d_exchange'8326'_276
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.exchange\8326"
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__528 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__528 v0 v1
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
               -> let v6 = d__'8799'T__528 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__528 (coe v3) (coe v5) in
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
               -> let v6 = d__'8799'T__528 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__528 (coe v3) (coe v5) in
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
               -> let v6 = d__'8799'T__528 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__528 (coe v3) (coe v5) in
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
               -> let v6 = d__'8799'T__528 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'T__528 (coe v3) (coe v5) in
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
               -> let v4 = d__'8799'T__528 (coe v2) (coe v3) in
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
d_InferElabResult_750 a0 a1 = ()
data T_InferElabResult_750
  = C_success_758 MAlonzo.Code.Once.Type.T_Type_4
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 |
    C_failure_760 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_762 = ()
data T_NamedCtx_762
  = C_mkCtx_776 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_770 :: T_NamedCtx_762 -> Integer
d_size_770 v0
  = case coe v0 of
      C_mkCtx_776 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_772 ::
  T_NamedCtx_762 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14]
d_named_772 v0
  = case coe v0 of
      C_mkCtx_776 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_774 ::
  T_NamedCtx_762 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_774 v0
  = case coe v0 of
      C_mkCtx_776 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_778 :: T_NamedCtx_762
d_emptyCtx_778
  = coe
      C_mkCtx_776 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_32)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_780 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_4 -> T_NamedCtx_762
d_extendNamedCtx_780 v0 v1 v2
  = case coe v0 of
      C_mkCtx_776 v3 v4 v5
        -> coe
             C_mkCtx_776 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__34 (coe v4)
                (coe v1) (coe v2))
             (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'__12 v5 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.lookupVar
d_lookupVar_796 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupVar_796 v0 v1
  = case coe v0 of
      C_mkCtx_776 v2 v3 v4
        -> coe du_go_816 (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_816 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_816 ~v0 ~v1 ~v2 v3 v4 v5 v6 = du_go_816 v3 v4 v5 v6
du_go_816 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_14] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_816 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
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
                                                   du_go_816 (coe v0) (coe v9) (coe v5) (coe v7) in
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
                                                                  d_weaken_174 (coe v9) (coe v7)
                                                                  (coe v8) (coe v15) (coe v16)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v13
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_882 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_750
d_inferElab_882 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     du_go_816 (coe v2) (coe d_size_770 (coe v0))
                     (coe d_named_772 (coe v0)) (coe d_debruijn_774 (coe v0)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe C_success_758 (coe v5) (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_760
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Unbound variable: " :: Data.Text.Text) v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v2 v3
        -> coe
             du_inferApp_942 (coe v0) (coe v3)
             (coe d_inferElab_882 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v2 v3
        -> let v4
                 = d_inferElab_882
                     (coe
                        d_extendNamedCtx_780 (coe v0) (coe v2)
                        (coe
                           MAlonzo.Code.Once.Type.C_TVar_28 (coe ("\945" :: Data.Text.Text))))
                     (coe v3) in
           coe
             (case coe v4 of
                C_success_758 v5 v6
                  -> coe
                       C_success_758
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658'__14
                          (coe
                             MAlonzo.Code.Once.Type.C_TVar_28 (coe ("\945" :: Data.Text.Text)))
                          (coe v5))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_46 v6)
                C_failure_760 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v2 v3 v4
        -> let v5 = d_inferElab_882 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_758 v6 v7
                  -> let v8
                           = d_inferElab_882
                               (coe d_extendNamedCtx_780 (coe v0) (coe v2) (coe v6)) (coe v4) in
                     coe
                       (case coe v8 of
                          C_success_758 v9 v10
                            -> coe
                                 C_success_758 (coe v9)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_let''_142 v6 v7 v10)
                          C_failure_760 v9 -> coe v8
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_760 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v2 v3
        -> let v4 = d_inferElab_882 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_758 v5 v6
                  -> let v7 = d_inferElab_882 (coe v0) (coe v3) in
                     coe
                       (case coe v7 of
                          C_success_758 v8 v9
                            -> coe
                                 C_success_758
                                 (coe MAlonzo.Code.Once.Type.C__'42'__10 (coe v5) (coe v8))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_66 v6 v9)
                          C_failure_760 v8 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_760 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RCase_46 v2 v3 v4 v5 v6
        -> coe
             du_inferCase_1120 (coe v0) (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_inferElab_882 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48
        -> coe
             C_success_758 (coe MAlonzo.Code.Once.Type.C_Unit_6)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_124)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v2
        -> coe
             C_failure_760
             (coe
                ("Integer literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v2
        -> coe
             C_failure_760
             (coe
                ("String literals not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v2 v3
        -> coe d_inferElab_882 (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v2 v3 v4
        -> coe
             C_failure_760
             (coe
                ("Binary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v3
        -> coe
             C_failure_760
             (coe
                ("Unary operators not supported in verified elaboration"
                 ::
                 Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferApp
d_inferApp_942 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_750 -> T_InferElabResult_750
d_inferApp_942 v0 ~v1 v2 v3 = du_inferApp_942 v0 v2 v3
du_inferApp_942 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_750 -> T_InferElabResult_750
du_inferApp_942 v0 v1 v2
  = case coe v2 of
      C_success_758 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__10 v5 v6
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__12 v5 v6
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'8658'__14 v5 v6
               -> coe
                    du_inferArg_956 (coe v5) (coe v6) (coe v4)
                    (coe d_inferElab_882 (coe v0) (coe v1))
             MAlonzo.Code.Once.Type.C_Eff_16 v5 v6
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_18 v5
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_28 v5
               -> coe
                    C_failure_760
                    (coe ("Expected function type in application" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_760 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferArg
d_inferArg_956 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
d_inferArg_956 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_inferArg_956 v3 v4 v5 v6
du_inferArg_956 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
du_inferArg_956 v0 v1 v2 v3
  = case coe v3 of
      C_success_758 v4 v5
        -> let v6 = d__'8799'T__528 (coe v0) (coe v4) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe
                              seq (coe v8)
                              (coe
                                 C_success_758 (coe v1)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_app_56 v4 v2 v5))
                       else coe
                              seq (coe v8)
                              (coe
                                 C_failure_760
                                 (coe ("Type mismatch in application" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_760 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.inferCase
d_inferCase_1120 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_750 -> T_InferElabResult_750
d_inferCase_1120 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferCase_1120 v0 v2 v3 v4 v5 v6
du_inferCase_1120 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_750 -> T_InferElabResult_750
du_inferCase_1120 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_758 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_Unit_6
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Void_8
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'42'__10 v8 v9
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C__'43'__12 v8 v9
               -> coe
                    du_inferLeft_1134 (coe v0) (coe v3) (coe v4) (coe v8) (coe v9)
                    (coe v7)
                    (coe
                       d_inferElab_882
                       (coe d_extendNamedCtx_780 (coe v0) (coe v1) (coe v8)) (coe v2))
             MAlonzo.Code.Once.Type.C__'8658'__14 v8 v9
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Eff_16 v8 v9
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Fix_18 v8
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Int_20
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Float_22
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Str_24
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_Buffer_26
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             MAlonzo.Code.Once.Type.C_TVar_28 v8
               -> coe
                    C_failure_760 (coe ("Expected sum type in case" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_760 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._.inferLeft
d_inferLeft_1134 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
d_inferLeft_1134 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_inferLeft_1134 v0 v4 v5 v6 v7 v8 v9
du_inferLeft_1134 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
du_inferLeft_1134 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_success_758 v7 v8
        -> coe
             du_inferRight_1146 (coe v3) (coe v4) (coe v5) (coe v7) (coe v8)
             (coe
                d_inferElab_882
                (coe d_extendNamedCtx_780 (coe v0) (coe v1) (coe v4)) (coe v2))
      C_failure_760 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._._._.inferRight
d_inferRight_1146 ::
  T_NamedCtx_762 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
d_inferRight_1146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_inferRight_1146 v6 v7 v8 v9 v10 v11
du_inferRight_1146 ::
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_28 ->
  T_InferElabResult_750 -> T_InferElabResult_750
du_inferRight_1146 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_success_758 v6 v7
        -> let v8 = d__'8799'T__528 (coe v3) (coe v6) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe
                              seq (coe v10)
                              (coe
                                 C_success_758 (coe v6)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_case''_118 v0 v1 v2 v4 v7))
                       else coe
                              seq (coe v10)
                              (coe
                                 C_failure_760
                                 (coe ("Case branches have different types" :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_760 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_1172 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_1172 v0
  = let v1 = d_inferElab_882 (coe d_emptyCtx_778) (coe v0) in
    coe
      (case coe v1 of
         C_success_758 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v2)
                      (coe v3)))
         C_failure_760 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_1190 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_4 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_4
d_compileExprTyped_1190 v0 v1
  = let v2 = d_inferElab_882 (coe d_emptyCtx_778) (coe v0) in
    coe
      (case coe v2 of
         C_success_758 v3 v4
           -> let v5 = d__'8799'T__528 (coe v1) (coe v3) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                     -> if coe v6
                          then coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_70
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v3)
                                       (coe v4)))
                          else coe
                                 seq (coe v7) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_failure_760 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
