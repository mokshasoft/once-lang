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

module MAlonzo.Code.Once.Surface.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Syntax.Expr
d_Expr_8 a0 a1 a2 a3 = ()
data T_Expr_8
  = C_var_16 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_32 MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_8 |
    C_app_48 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Type.T_Type_108
             MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_8 T_Expr_8 |
    C_effApp_62 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 T_Expr_8 |
    C_pair_76 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fst''_88 MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 |
    C_snd''_100 MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 |
    C_inl''_112 T_Expr_8 | C_inr''_124 T_Expr_8 |
    C_case''_146 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.Type.T_Type_108
                 T_Expr_8 T_Expr_8 T_Expr_8 |
    C_unit_152 | C_absurd_162 T_Expr_8 |
    C_let''_178 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Type.T_Quantity_4
                MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 T_Expr_8 |
    C_int_184 Integer |
    C_str_190 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_float_198 MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 |
    C_add_208 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_sub_218 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_mul_228 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fadd_238 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fsub_248 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fmul_258 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fdiv_268 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_i2f_276 T_Expr_8 |
    C_div_286 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_mod''_296 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_neg_304 T_Expr_8 |
    C_lt_314 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_le_324 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_gt_334 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_ge_344 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_eq_354 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_ne_364 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_arr''_376 T_Expr_8 |
    C_sigOp_384 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_closure_392 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_402 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_lift'45'morphism_414 MAlonzo.Code.Once.IR.T_IR_16 |
    C_morph'45'app_426 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.IR.T_IR_16
                       T_Expr_8 |
    C_cata_438 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
               T_Expr_8 |
    C_ana_450 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
              T_Expr_8
-- Once.Surface.Syntax.svar→expr
d_svar'8594'expr_460 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 -> T_Expr_8
d_svar'8594'expr_460 ~v0 ~v1 ~v2 ~v3 v4 = du_svar'8594'expr_460 v4
du_svar'8594'expr_460 ::
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 -> T_Expr_8
du_svar'8594'expr_460 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_svar_218 v3 -> coe C_var_16 v3
      _ -> MAlonzo.RTE.mazUnreachableError
