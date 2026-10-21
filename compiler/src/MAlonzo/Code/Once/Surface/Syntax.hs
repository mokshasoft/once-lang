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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Surface.Syntax.Expr
d_Expr_8 a0 a1 a2 a3 = ()
data T_Expr_8
  = C_var_16 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_34 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_8 |
    C_app_50 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Type.T_Type_8
             MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_8 T_Expr_8 |
    C_effApp_68 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                MAlonzo.Code.Once.Internal.Context.T_Usage_46
                MAlonzo.Code.Once.Internal.Type.T_Type_8
                MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 T_Expr_8 T_Expr_8 |
    C_pair_82 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fst''_94 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Expr_8 |
    C_snd''_106 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Expr_8 |
    C_inl''_118 T_Expr_8 | C_inr''_130 T_Expr_8 |
    C_case''_152 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Expr_8 T_Expr_8
                 T_Expr_8 |
    C_unit_158 | C_absurd_168 T_Expr_8 |
    C_let''_184 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                MAlonzo.Code.Once.Internal.Context.T_Usage_46
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Expr_8 T_Expr_8 |
    C_int_190 Integer |
    C_float_198 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 |
    C_add_208 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_sub_218 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_mul_228 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fadd_238 MAlonzo.Code.Once.Internal.Context.T_Usage_46
               MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fsub_248 MAlonzo.Code.Once.Internal.Context.T_Usage_46
               MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fmul_258 MAlonzo.Code.Once.Internal.Context.T_Usage_46
               MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fdiv_268 MAlonzo.Code.Once.Internal.Context.T_Usage_46
               MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_i2f_276 T_Expr_8 |
    C_div_286 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_mod''_296 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_neg_304 T_Expr_8 |
    C_lt_314 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_le_324 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_gt_334 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_ge_344 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_eq_354 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_ne_364 MAlonzo.Code.Once.Internal.Context.T_Usage_46
             MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_coerce_376 MAlonzo.Code.Once.Internal.Type.T_Type_8
                 MAlonzo.Code.Once.Internal.Type.Sub.T__'60''58'__12 T_Expr_8 |
    C_sigOp_384 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_34 |
    C_closure_392 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_402 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_closed_410 T_Expr_8 |
    C_lift'45'morphism_422 MAlonzo.Code.Once.IR.T_IR_16 |
    C_morph'45'app_434 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                       MAlonzo.Code.Once.Internal.Type.T_Type_8
                       MAlonzo.Code.Once.IR.T_IR_16 T_Expr_8 |
    C_comp''_452 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Internal.Type.T_Type_8 T_Expr_8 T_Expr_8 |
    C_copair''_470 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                   MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_fork''_488 MAlonzo.Code.Once.Internal.Context.T_Usage_46
                 MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8 T_Expr_8 |
    C_curry''_506 T_Expr_8 |
    C_cata_520 MAlonzo.Code.Once.Internal.Context.T_Usage_46
               MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48
               T_Expr_8 |
    C_ana_536 MAlonzo.Code.Once.Internal.Context.T_Usage_46
              MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48
              T_Expr_8 |
    C_loop_548 MAlonzo.Code.Once.Internal.Context.T_Usage_46 T_Expr_8
-- Once.Surface.Syntax.svar→expr
d_svar'8594'expr_558 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_112 -> T_Expr_8
d_svar'8594'expr_558 ~v0 ~v1 ~v2 ~v3 v4 = du_svar'8594'expr_558 v4
du_svar'8594'expr_558 ::
  MAlonzo.Code.Once.Internal.Context.T_SVar_112 -> T_Expr_8
du_svar'8594'expr_558 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Context.C_svar_120 v3 -> coe C_var_16 v3
      _ -> MAlonzo.RTE.mazUnreachableError
