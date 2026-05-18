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

module MAlonzo.Code.Once.Surface.Elaborate where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_274
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_const_416
         (coe MAlonzo.Code.Once.Type.C_fits'45'int_190) v0
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286
      (coe MAlonzo.Code.Once.Type.C_Unit_118)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_SigOp_422
         (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_336
            (coe v0)))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_addIR_18
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_312
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_subIR_20
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_314
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_mulIR_22
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_316
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_divIR_24
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_318
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_modIR_26
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_320
-- Once.Surface.Elaborate.negIR
d_negIR_28 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_negIR_28
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_322
-- Once.Surface.Elaborate.ltIR
d_ltIR_30 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_ltIR_30
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_324
-- Once.Surface.Elaborate.leIR
d_leIR_32 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_leIR_32
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_326
-- Once.Surface.Elaborate.gtIR
d_gtIR_34 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_gtIR_34
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_328
-- Once.Surface.Elaborate.geIR
d_geIR_36 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_geIR_36
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_330
-- Once.Surface.Elaborate.eqIR
d_eqIR_38 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_eqIR_38
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_332
-- Once.Surface.Elaborate.neIR
d_neIR_40 :: MAlonzo.Code.Once.CCC.IR.T_IR_274
d_neIR_40
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_422
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_334
-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_44 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_'10214'_'10215''7580'_44 ~v0 v1 = du_'10214'_'10215''7580'_44 v1
du_'10214'_'10215''7580'_44 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_'10214'_'10215''7580'_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_118
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__122
             (coe du_'10214'_'10215''7580'_44 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.proj
d_proj_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_proj_58 ~v0 v1 v2 = du_proj_58 v1 v2
du_proj_58 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_proj_58 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.CCC.IR.C_snd_306
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                    (coe du_'10214'_'10215''7580'_44 (coe v3))
                    (coe du_proj_58 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_300)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_78 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_swap''_78 ~v0 ~v1 v2 = du_swap''_78 v2
du_swap''_78 ::
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_swap''_78 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
      (coe MAlonzo.Code.Once.CCC.IR.C_snd_306)
      (coe MAlonzo.Code.Once.CCC.IR.C_fst_300) v0
-- Once.Surface.Elaborate.distribute
d_distribute_88 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_distribute_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_108 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_swap''_78 (coe v3))
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_curryInlSwap_102 v0 v1 ~v2 v3 = du_curryInlSwap_102 v0 v1 v3
du_curryInlSwap_102 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_curryInlSwap_102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_344
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286
         (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.CCC.IR.C_inl_312 v2)
         (coe du_swap''_78 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_curryInrSwap_104 v0 ~v1 v2 v3 = du_curryInrSwap_104 v0 v2 v3
du_curryInrSwap_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_curryInrSwap_104 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_344
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__286
         (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.CCC.IR.C_inr_318 v2)
         (coe du_swap''_78 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_curryDistrib_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.IR.C_case_326
      (coe du_curryInlSwap_102 (coe v0) (coe v1) (coe v3))
      (coe du_curryInrSwap_104 (coe v0) (coe v2) (coe v3))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_distrib''_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__286
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_pure_34))
            (coe
               MAlonzo.Code.Once.Type.C__'43'__124
               (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_352)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
         (coe
            MAlonzo.Code.Once.CCC.IR.C__'8728'__286
            (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v1) (coe v2))
            (d_curryDistrib_106 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Once.CCC.IR.C_fst_300))
         (coe MAlonzo.Code.Once.CCC.IR.C_snd_306) v3)
-- Once.Surface.Elaborate.elaborate
d_elaborate_118 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_elaborate_118 ~v0 v1 ~v2 v3 v4 v5 = du_elaborate_118 v1 v3 v4 v5
du_elaborate_118 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CCC.IR.T_AllocMode_258 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_elaborate_118 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v6
        -> coe du_proj_58 (coe v0) (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v7 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_344
                    (coe
                       du_elaborate_118
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v13
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v15) (coe v2) (coe v12))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v6 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v8))
             (coe MAlonzo.Code.Once.CCC.IR.C_apply_352)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                      (coe v1))
                   (coe v2) (coe v11))
                (coe du_elaborate_118 (coe v0) (coe v8) (coe v2) (coe v12)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v6 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                       (coe MAlonzo.Code.Once.Type.C_Unit_118)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v14))
                    (coe MAlonzo.Code.Once.CCC.IR.C_arr_360)
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_curry_344
                       (coe
                          MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                          (coe du_'10214'_'10215''7580'_44 (coe v0))
                          (coe
                             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__122
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                                   (coe MAlonzo.Code.Once.Type.d_effK_62) (coe v14))
                                (coe v8))
                             (coe MAlonzo.Code.Once.CCC.IR.C_apply_352)
                             (coe
                                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                                (coe
                                   du_elaborate_118 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                                      (coe MAlonzo.Code.Once.Type.d_effK_62) (coe v14))
                                   (coe v2) (coe v10))
                                (coe du_elaborate_118 (coe v0) (coe v8) (coe v2) (coe v11)) v2))
                          (coe MAlonzo.Code.Once.CCC.IR.C_fst_300))
                       v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v6 v7 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                    (coe du_elaborate_118 (coe v0) (coe v12) (coe v2) (coe v10))
                    (coe du_elaborate_118 (coe v0) (coe v13) (coe v2) (coe v11)) v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v8))
             (coe MAlonzo.Code.Once.CCC.IR.C_fst_300)
             (coe
                du_elaborate_118 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v8))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v7 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v1))
             (coe MAlonzo.Code.Once.CCC.IR.C_snd_306)
             (coe
                du_elaborate_118 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v7) (coe v1))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v10
                    (coe MAlonzo.Code.Once.CCC.IR.C_inl_312 v2)
                    (coe du_elaborate_118 (coe v0) (coe v10) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v11
                    (coe MAlonzo.Code.Once.CCC.IR.C_inr_318 v2)
                    (coe du_elaborate_118 (coe v0) (coe v11) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'43'__124
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v11)))
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v12))))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_case_326
                (coe
                   du_elaborate_118
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v11))
                   (coe v1) (coe v2) (coe v15))
                (coe
                   du_elaborate_118
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v12))
                   (coe v1) (coe v2) (coe v16)))
             (coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__122
                   (coe du_'10214'_'10215''7580'_44 (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v11) (coe v12)))
                (d_distribute_88
                   (coe du_'10214'_'10215''7580'_44 (coe v0)) (coe v11) (coe v12)
                   (coe v2))
                (coe
                   MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                   (coe MAlonzo.Code.Once.CCC.IR.C_id_278)
                   (coe
                      du_elaborate_118 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v11) (coe v12))
                      (coe v2) (coe v14))
                   v2))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_330
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe MAlonzo.Code.Once.Type.C_Void_120)
             (coe MAlonzo.Code.Once.CCC.IR.C_initial_334)
             (coe
                du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_120)
                (coe v2) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v6 v7 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                du_'10214'_'10215''7580'_44
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v9)))
             (coe
                du_elaborate_118
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v9))
                (coe v1) (coe v2) (coe v12))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe MAlonzo.Code.Once.CCC.IR.C_id_278)
                (coe du_elaborate_118 (coe v0) (coe v9) (coe v2) (coe v11)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v6
        -> coe du_intLit_8 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v6
        -> coe du_strLit_14 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe MAlonzo.Code.Once.Type.C_Int_132) d_negIR_28
             (coe
                du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe v2) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_ltIR_30
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_leIR_32
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_gtIR_34
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_geIR_36
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_eqIR_38
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe
                MAlonzo.Code.Once.Type.C__'42'__122
                (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe MAlonzo.Code.Once.Type.C_Int_132))
             d_neIR_40
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_294
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_118 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_132)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v12))
                    (coe MAlonzo.Code.Once.CCC.IR.C_arr_360)
                    (coe
                       du_elaborate_118 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v12))
                       (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Once.CCC.IR.C__'8728'__286
                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
                     (coe
                        MAlonzo.Code.Once.CCC.IR.C_SigOp_422
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
                           (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v1) (coe v7)))
                     (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Once.CCC.IR.C_curry_344
                       (coe
                          MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v9
                          (coe
                             MAlonzo.Code.Once.CCC.IR.C_SigOp_422
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
                                (coe v9) (coe v11) (coe v7)))
                          (coe MAlonzo.Code.Once.CCC.IR.C_snd_306))
                       v2
                _ -> coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v6
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286
             (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_SigOp_422
                (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
                   (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v1) (coe v6)))
             (coe MAlonzo.Code.Once.CCC.IR.C_terminal_330)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_514 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_344
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v9 v8
                       (coe MAlonzo.Code.Once.CCC.IR.C_snd_306))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_526 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__286 v7 v9
             (coe du_elaborate_118 (coe v0) (coe v7) (coe v2) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_302 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
d_elaborate'45'default_302 ~v0 v1 ~v2 v3
  = du_elaborate'45'default_302 v1 v3
du_elaborate'45'default_302 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274
du_elaborate'45'default_302 v0 v1
  = coe
      du_elaborate_118 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_262)
