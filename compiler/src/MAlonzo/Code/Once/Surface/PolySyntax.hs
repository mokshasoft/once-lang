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

module MAlonzo.Code.Once.Surface.PolySyntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified Unsafe.Coerce
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.PolySyntax.PolyCtx
d_PolyCtx_6 a0 = ()
data T_PolyCtx_6
  = C_P'8709'_8 |
    C__P'44'_'94'__12 T_PolyCtx_6 MAlonzo.Code.Once.Type.T_PolyType_70
                      MAlonzo.Code.Once.Type.T_Quantity_4
-- Once.Surface.PolySyntax._P,_
d__P'44'__16 ::
  Integer ->
  T_PolyCtx_6 -> MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCtx_6
d__P'44'__16 ~v0 v1 v2 = du__P'44'__16 v1 v2
du__P'44'__16 ::
  T_PolyCtx_6 -> MAlonzo.Code.Once.Type.T_PolyType_70 -> T_PolyCtx_6
du__P'44'__16 v0 v1
  = coe
      C__P'44'_'94'__12 v0 v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
-- Once.Surface.PolySyntax.lookupPoly
d_lookupPoly_24 ::
  Integer ->
  T_PolyCtx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_PolyType_70
d_lookupPoly_24 ~v0 v1 v2 = du_lookupPoly_24 v1 v2
du_lookupPoly_24 ::
  T_PolyCtx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_PolyType_70
du_lookupPoly_24 v0 v1
  = case coe v0 of
      C__P'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupPoly_24 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.PolySyntax.lookupPolyQuantity
d_lookupPolyQuantity_38 ::
  Integer ->
  T_PolyCtx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
d_lookupPolyQuantity_38 ~v0 v1 v2 = du_lookupPolyQuantity_38 v1 v2
du_lookupPolyQuantity_38 ::
  T_PolyCtx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Quantity_4
du_lookupPolyQuantity_38 v0 v1
  = case coe v0 of
      C__P'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v5
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_lookupPolyQuantity_38 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.PolySyntax.PolyExpr
d_PolyExpr_52 a0 a1 a2 = ()
data T_PolyExpr_52
  = C_pvar_60 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_plam_72 T_PolyExpr_52 |
    C_papp_84 MAlonzo.Code.Once.Type.T_PolyType_70
              MAlonzo.Code.Once.Type.T_Quantity_4 T_PolyExpr_52 T_PolyExpr_52 |
    C_peffApp_94 MAlonzo.Code.Once.Type.T_PolyType_70 T_PolyExpr_52
                 T_PolyExpr_52 |
    C_ppair_104 T_PolyExpr_52 T_PolyExpr_52 |
    C_pfst''_114 MAlonzo.Code.Once.Type.T_PolyType_70 T_PolyExpr_52 |
    C_psnd''_124 MAlonzo.Code.Once.Type.T_PolyType_70 T_PolyExpr_52 |
    C_pinl''_134 T_PolyExpr_52 | C_pinr''_144 T_PolyExpr_52 |
    C_pcase''_156 MAlonzo.Code.Once.Type.T_PolyType_70
                  MAlonzo.Code.Once.Type.T_PolyType_70 T_PolyExpr_52 T_PolyExpr_52
                  T_PolyExpr_52 |
    C_punit_162 | C_pabsurd_170 T_PolyExpr_52 |
    C_plet''_180 MAlonzo.Code.Once.Type.T_PolyType_70 T_PolyExpr_52
                 T_PolyExpr_52 |
    C_pint_186 Integer |
    C_pstr_192 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_padd_198 T_PolyExpr_52 T_PolyExpr_52 |
    C_psub_204 T_PolyExpr_52 T_PolyExpr_52 |
    C_pmul_210 T_PolyExpr_52 T_PolyExpr_52 |
    C_pdiv_216 T_PolyExpr_52 T_PolyExpr_52 |
    C_pmod''_222 T_PolyExpr_52 T_PolyExpr_52 |
    C_pneg_228 T_PolyExpr_52 | C_plt_234 T_PolyExpr_52 T_PolyExpr_52 |
    C_ple_240 T_PolyExpr_52 T_PolyExpr_52 |
    C_pgt_246 T_PolyExpr_52 T_PolyExpr_52 |
    C_pge_252 T_PolyExpr_52 T_PolyExpr_52 |
    C_peq_258 T_PolyExpr_52 T_PolyExpr_52 |
    C_pne_264 T_PolyExpr_52 T_PolyExpr_52 |
    C_parr''_274 T_PolyExpr_52 |
    C_pprim_282 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Surface.PolySyntax.extractCtx
d_extractCtx_286 ::
  Integer ->
  T_PolyCtx_6 -> Maybe MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_extractCtx_286 ~v0 v1 = du_extractCtx_286 v1
du_extractCtx_286 ::
  T_PolyCtx_6 -> Maybe MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
du_extractCtx_286 v0
  = case coe v0 of
      C_P'8709'_8
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      C__P'44'_'94'__12 v2 v3 v4
        -> let v5 = coe du_extractCtx_286 (coe v2) in
           coe
             (let v6 = MAlonzo.Code.Once.Type.d_extract_144 (coe v3) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v4)
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.PolySyntax.unsafeCoerceExpr
-- Patched: use unsafeCoerce instead of error (types are erased at runtime)
d_unsafeCoerceExpr_324 _ _ _ _ _ = Unsafe.Coerce.unsafeCoerce
-- Once.Surface.PolySyntax.extractExpr
d_extractExpr_336 ::
  Integer ->
  T_PolyCtx_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  T_PolyExpr_52 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  Maybe MAlonzo.Code.Once.Surface.Syntax.T_Expr_162
d_extractExpr_336 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
      (coe d_unsafeCoerceExpr_324 v0 v1 v4 v2 v5 v3)
-- Once.Surface.PolySyntax.pweaken
-- Patched: use unsafeCoerce instead of error (de Bruijn weakening is identity at runtime)
d_pweaken_354 _ _ _ _ _ = Unsafe.Coerce.unsafeCoerce
-- Once.Surface.PolySyntax.pweakenFromEmpty
d_pweakenFromEmpty_362 ::
  Integer ->
  T_PolyCtx_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_70 ->
  T_PolyExpr_52 -> T_PolyExpr_52
d_pweakenFromEmpty_362 v0 v1 v2 v3
  = case coe v1 of
      C_P'8709'_8 -> coe v3
      C__P'44'_'94'__12 v5 v6 v7
        -> let v8 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                d_pweaken_354 v8 v5 v2 v6 v7
                (d_pweakenFromEmpty_362 (coe v8) (coe v5) (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
