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
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Concrete

-- Once.Surface.Syntax.Expr
d_Expr_10 a0 a1 a2 a3 a4 = ()
data T_Expr_10
  = C_var_20 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_38 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_10 |
    C_app_54 MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.Spec.Type.T_Ty_8
             MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 T_Expr_10 T_Expr_10 |
    C_effApp_74 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68 T_Expr_10 T_Expr_10 |
    C_pair_88 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fst''_100 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 |
    C_snd''_112 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 |
    C_inl''_124 T_Expr_10 | C_inr''_136 T_Expr_10 |
    C_case''_158 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 T_Expr_10 |
    C_unit_164 | C_absurd_174 T_Expr_10 |
    C_let''_190 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Context.T_Usage_34
                MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 |
    C_int_196 Integer |
    C_float_204 MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 |
    C_num_218 MAlonzo.Code.Once.Spec.Theory.T_NumTy_6
              MAlonzo.Code.Once.Spec.Theory.T_Theory_16
              MAlonzo.Code.Once.Spec.Theory.T_Shape_30
              MAlonzo.Code.Once.Spec.Theory.T_Has_104
              MAlonzo.Code.Once.Spec.Theory.T_Sym_38 T_Expr_10 |
    C_coerce_230 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                 MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 T_Expr_10 |
    C_sigOp_238 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 |
    C_closure_246 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_poly_256 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_closed_264 T_Expr_10 |
    C_lift'45'morphism_276 MAlonzo.Code.Once.IR.T_IR_16 |
    C_morph'45'app_288 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Spec.Type.T_Ty_8 MAlonzo.Code.Once.IR.T_IR_16
                       T_Expr_10 |
    C_comp''_306 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Expr_10 T_Expr_10 |
    C_copair''_324 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                   MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_fork''_342 MAlonzo.Code.Once.Spec.Context.T_Usage_34
                 MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10 T_Expr_10 |
    C_curry''_360 T_Expr_10 |
    C_cata_376 MAlonzo.Code.Once.Spec.Context.T_Usage_34
               (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                MAlonzo.Code.Once.Spec.Type.T_Kind_70)
               MAlonzo.Code.Once.Spec.Type.T_WFFun_118 T_Expr_10 |
    C_ana_394 MAlonzo.Code.Once.Spec.Context.T_Usage_34
              (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
               MAlonzo.Code.Once.Spec.Type.T_Kind_70)
              MAlonzo.Code.Once.Spec.Type.T_WFFun_118 T_Expr_10 |
    C_loop_406 MAlonzo.Code.Once.Spec.Context.T_Usage_34 T_Expr_10
-- Once.Surface.Syntax.svar→expr
d_svar'8594'expr_418 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Context.T_SVar_36 -> T_Expr_10
d_svar'8594'expr_418 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_svar'8594'expr_418 v5
du_svar'8594'expr_418 ::
  MAlonzo.Code.Once.Context.T_SVar_36 -> T_Expr_10
du_svar'8594'expr_418 v0
  = case coe v0 of
      MAlonzo.Code.Once.Context.C_svar_46 v3 -> coe C_var_20 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.appT
d_appT_440 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_Expr_10 -> T_Expr_10 -> T_Expr_10
d_appT_440 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 v7 v8 v9 v10
  = du_appT_440 v3 v4 v5 v7 v8 v9 v10
du_appT_440 ::
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_Expr_10 -> T_Expr_10 -> T_Expr_10
du_appT_440 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v7
        -> case coe v7 of
             MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
               -> coe C_app_54 v0 v1 v2 v3 v5 v6
             MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
               -> coe
                    C_effApp_74 v0 v1 v2 v3
                    (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'act_70) v5 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe
             C_effApp_74 v0 v1 v2 v3
             (coe MAlonzo.Code.Once.Spec.Grade.C_eg'45'eff_72) v5 v6
      _ -> MAlonzo.RTE.mazUnreachableError
