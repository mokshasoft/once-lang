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
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Surface.Syntax.Expr
d_Expr_10 a0 a1 a2 a3 a4 = ()
data T_Expr_10
  = C_var_20 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_38 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_10 |
    C_app_54 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Type.T_Ty_8
             MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_10 T_Expr_10 |
    C_effApp_72 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 T_Expr_10 T_Expr_10 |
    C_pair_86 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fst''_98 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 |
    C_snd''_110 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 |
    C_inl''_122 T_Expr_10 | C_inr''_134 T_Expr_10 |
    C_case''_156 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 T_Expr_10 |
    C_unit_162 | C_absurd_172 T_Expr_10 |
    C_let''_188 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 |
    C_int_194 Integer |
    C_float_202 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 |
    C_add_212 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_sub_222 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_mul_232 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fadd_242 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fsub_252 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fmul_262 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fdiv_272 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_i2f_280 T_Expr_10 |
    C_div_290 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_mod''_300 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_neg_308 T_Expr_10 |
    C_lt_318 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_le_328 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_gt_338 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_ge_348 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_eq_358 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_ne_368 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_coerce_380 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 T_Expr_10 |
    C_sigOp_388 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_8 |
    C_closure_396 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_406 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_closed_414 T_Expr_10 |
    C_lift'45'morphism_426 MAlonzo.Code.Once.IR.T_IR_16 |
    C_morph'45'app_438 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Type.T_Ty_8 MAlonzo.Code.Once.IR.T_IR_16
                       T_Expr_10 |
    C_comp''_456 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 |
    C_copair''_474 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fork''_492 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_curry''_510 T_Expr_10 |
    C_cata_526 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                MAlonzo.Code.Once.Spec.Type.T_Kind_70)
               MAlonzo.Code.Once.Spec.Type.T_WFFun_118 T_Expr_10 |
    C_ana_544 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Type.T_Kind_70)
              MAlonzo.Code.Once.Spec.Type.T_WFFun_118 T_Expr_10 |
    C_loop_556 MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10
-- Once.Surface.Syntax.svar→expr
d_svar'8594'expr_568 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Context.T_SVar_38 -> T_Expr_10
d_svar'8594'expr_568 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_svar'8594'expr_568 v5
du_svar'8594'expr_568 ::
  MAlonzo.Code.Once.Internal.Context.T_SVar_38 -> T_Expr_10
du_svar'8594'expr_568 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Context.C_svar_48 v3 -> coe C_var_20 v3
      _ -> MAlonzo.RTE.mazUnreachableError
