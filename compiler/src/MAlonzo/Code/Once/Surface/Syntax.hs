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
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Surface.Syntax.Expr
d_Expr_8 a0 a1 a2 a3 = ()
data T_Expr_8
  = C_var_16 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_34 MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_8 |
    C_app_50 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Type.T_Type_108
             MAlonzo.Code.Once.Type.T_Quantity_4 T_Expr_8 T_Expr_8 |
    C_effApp_64 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 T_Expr_8 |
    C_pair_78 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fst''_90 MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 |
    C_snd''_102 MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 |
    C_inl''_114 T_Expr_8 | C_inr''_126 T_Expr_8 |
    C_case''_148 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.Type.T_Type_108
                 T_Expr_8 T_Expr_8 T_Expr_8 |
    C_unit_154 | C_absurd_164 T_Expr_8 |
    C_let''_180 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Type.T_Quantity_4
                MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 T_Expr_8 |
    C_int_186 Integer |
    C_str_192 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_float_200 MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 |
    C_add_210 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_sub_220 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_mul_230 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fadd_240 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fsub_250 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fmul_260 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fdiv_270 MAlonzo.Code.Once.Surface.Context.T_Usage_60
               MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_i2f_278 T_Expr_8 |
    C_div_288 MAlonzo.Code.Once.Surface.Context.T_Usage_60
              MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_mod''_298 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_neg_306 T_Expr_8 |
    C_lt_316 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_le_326 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_gt_336 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_ge_346 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_eq_356 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_ne_366 MAlonzo.Code.Once.Surface.Context.T_Usage_60
             MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_coerce_378 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.Sub.T__'60''58'__44 T_Expr_8 |
    C_sigOp_386 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 |
    C_closure_394 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_404 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_lift'45'morphism_416 MAlonzo.Code.Once.IR.T_IR_16 |
    C_morph'45'app_428 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.IR.T_IR_16
                       T_Expr_8 |
    C_comp''_446 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Type.T_Type_108 T_Expr_8 T_Expr_8 |
    C_copair''_464 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                   MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_fork''_482 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60 T_Expr_8 T_Expr_8 |
    C_curry''_500 T_Expr_8 |
    C_cata_512 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
               T_Expr_8 |
    C_ana_526 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240
              T_Expr_8
-- Once.Surface.Syntax.svar→expr
d_svar'8594'expr_536 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 -> T_Expr_8
d_svar'8594'expr_536 ~v0 ~v1 ~v2 ~v3 v4 = du_svar'8594'expr_536 v4
du_svar'8594'expr_536 ::
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 -> T_Expr_8
du_svar'8594'expr_536 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_svar_218 v3 -> coe C_var_16 v3
      _ -> MAlonzo.RTE.mazUnreachableError
