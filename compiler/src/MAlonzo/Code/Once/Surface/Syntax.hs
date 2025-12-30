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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Surface.Syntax.Ctx
d_Ctx_6 a0 = ()
data T_Ctx_6
  = C_'8709'_8 | C__'44'__12 T_Ctx_6 MAlonzo.Code.Once.Type.T_Type_4
-- Once.Surface.Syntax.lookup
d_lookup_16 ::
  Integer ->
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_4
d_lookup_16 ~v0 v1 v2 = du_lookup_16 v1 v2
du_lookup_16 ::
  T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_4
du_lookup_16 v0 v1
  = case coe v0 of
      C__'44'__12 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookup_16 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Syntax.Expr
d_Expr_28 a0 a1 a2 = ()
data T_Expr_28
  = C_var_36 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_lam_46 T_Expr_28 |
    C_app_56 MAlonzo.Code.Once.Type.T_Type_4 T_Expr_28 T_Expr_28 |
    C_pair_66 T_Expr_28 T_Expr_28 |
    C_fst''_76 MAlonzo.Code.Once.Type.T_Type_4 T_Expr_28 |
    C_snd''_86 MAlonzo.Code.Once.Type.T_Type_4 T_Expr_28 |
    C_inl''_96 T_Expr_28 | C_inr''_106 T_Expr_28 |
    C_case''_118 MAlonzo.Code.Once.Type.T_Type_4
                 MAlonzo.Code.Once.Type.T_Type_4 T_Expr_28 T_Expr_28 T_Expr_28 |
    C_unit_124 | C_absurd_132 T_Expr_28 |
    C_let''_142 MAlonzo.Code.Once.Type.T_Type_4 T_Expr_28 T_Expr_28 |
    C_int_148 Integer |
    C_binop_156 MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 T_Expr_28
                T_Expr_28 |
    C_builtin_164 MAlonzo.Code.Agda.Builtin.String.T_String_6
