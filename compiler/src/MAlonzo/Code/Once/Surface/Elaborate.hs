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
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.Arith.SigOp.IntLit
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_12
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe MAlonzo.Code.Once.Type.C_Unit_136)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_SigOp_156
         (MAlonzo.Code.Once.Arith.SigOp.IntLit.d_lit'45'int'45'info_12
            (coe v0)))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe MAlonzo.Code.Once.Type.C_Unit_136)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_SigOp_156
         (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_336
            (coe v0)))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_addIR_18
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_312
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_subIR_20
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_314
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_mulIR_22
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_316
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_divIR_24
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_318
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_modIR_26
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_320
-- Once.Surface.Elaborate.negIR
d_negIR_28 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_negIR_28
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_322
-- Once.Surface.Elaborate.ltIR
d_ltIR_30 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_ltIR_30
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_324
-- Once.Surface.Elaborate.leIR
d_leIR_32 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_leIR_32
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_326
-- Once.Surface.Elaborate.gtIR
d_gtIR_34 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_gtIR_34
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_328
-- Once.Surface.Elaborate.geIR
d_geIR_36 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_geIR_36
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_330
-- Once.Surface.Elaborate.eqIR
d_eqIR_38 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_eqIR_38
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_332
-- Once.Surface.Elaborate.neIR
d_neIR_40 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_neIR_40
  = coe
      MAlonzo.Code.Once.CCC.IR.C_SigOp_156
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_334
-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_44 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126
d_'10214'_'10215''7580'_44 ~v0 v1 = du_'10214'_'10215''7580'_44 v1
du_'10214'_'10215''7580'_44 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126
du_'10214'_'10215''7580'_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_136
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__140
             (coe du_'10214'_'10215''7580'_44 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.proj
d_proj_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_proj_58 ~v0 v1 v2 = du_proj_58 v1 v2
du_proj_58 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_proj_58 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.CCC.IR.C_snd_44
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                    (coe du_'10214'_'10215''7580'_44 (coe v3))
                    (coe du_proj_58 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_78 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_swap''_78 ~v0 ~v1 = du_swap''_78
du_swap''_78 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
du_swap''_78
  = coe
      MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
      (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
      (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
-- Once.Surface.Elaborate.distribute
d_distribute_86 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_distribute_86 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe
         MAlonzo.Code.Once.Type.C__'42'__140
         (coe MAlonzo.Code.Once.Type.C__'43'__142 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_104 (coe v0) (coe v1) (coe v2)) (coe du_swap''_78)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryInlSwap_98 v0 v1 ~v2 = du_curryInlSwap_98 v0 v1
du_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_curryInlSwap_98 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_82
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__24
         (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.IR.C_inl_50
            (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryInrSwap_100 v0 ~v1 v2 = du_curryInrSwap_100 v0 v2
du_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_curryInrSwap_100 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_82
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__24
         (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.IR.C_inr_56
            (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_102 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryDistrib_102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_case_64
      (coe du_curryInlSwap_98 (coe v0) (coe v1))
      (coe du_curryInrSwap_100 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_104 ::
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_distrib''_104 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe
         MAlonzo.Code.Once.Type.C__'42'__140
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_54
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_pure_38))
            (coe
               MAlonzo.Code.Once.Type.C__'43'__142
               (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
         (coe
            MAlonzo.Code.Once.CCC.IR.C__'8728'__24
            (coe MAlonzo.Code.Once.Type.C__'43'__142 (coe v1) (coe v2))
            (d_curryDistrib_102 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.CCC.IR.C_fst_38))
         (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
-- Once.Surface.Elaborate.elaborate
d_elaborate_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_elaborate_114 ~v0 v1 ~v2 v3 v4 = du_elaborate_114 v1 v3 v4
du_elaborate_114 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_126 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_elaborate_114 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v5
        -> coe du_proj_58 (coe v0) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v6 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_82
                    (coe
                       du_elaborate_114
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v12
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v14) (coe v11))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v5 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v7)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_54 (coe v9)
                      (coe MAlonzo.Code.Once.Type.C_pure_38))
                   (coe v1))
                (coe v7))
             (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v7)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_54 (coe v9)
                         (coe MAlonzo.Code.Once.Type.C_pure_38))
                      (coe v1))
                   (coe v10))
                (coe du_elaborate_114 (coe v0) (coe v7) (coe v11))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v5 v6 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144
                       (coe MAlonzo.Code.Once.Type.C_Unit_136)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_54
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_38))
                       (coe v13))
                    (coe MAlonzo.Code.Once.CCC.IR.C_arr_98)
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_curry_82
                       (coe
                          MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                          (coe du_'10214'_'10215''7580'_44 (coe v0))
                          (coe
                             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__140
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v7)
                                   (coe MAlonzo.Code.Once.Type.d_effK_66) (coe v13))
                                (coe v7))
                             (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
                             (coe
                                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                                (coe
                                   du_elaborate_114 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v7)
                                      (coe MAlonzo.Code.Once.Type.d_effK_66) (coe v13))
                                   (coe v9))
                                (coe du_elaborate_114 (coe v0) (coe v7) (coe v10))
                                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)))
                          (coe MAlonzo.Code.Once.CCC.IR.C_fst_38))
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v5 v6 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__140 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (coe du_elaborate_114 (coe v0) (coe v11) (coe v9))
                    (coe du_elaborate_114 (coe v0) (coe v12) (coe v10))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v1) (coe v7))
             (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
             (coe
                du_elaborate_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v1) (coe v7))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v6 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v6) (coe v1))
             (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
             (coe
                du_elaborate_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__140 (coe v6) (coe v1))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__142 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v9
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_inl_50
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
                    (coe du_elaborate_114 (coe v0) (coe v9) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__142 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v10
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_inr_56
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
                    (coe du_elaborate_114 (coe v0) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'43'__142
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v10)))
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v11))))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_case_64
                (coe
                   du_elaborate_114
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v10))
                   (coe v1) (coe v14))
                (coe
                   du_elaborate_114
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v11))
                   (coe v1) (coe v15)))
             (coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__140
                   (coe du_'10214'_'10215''7580'_44 (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__142 (coe v10) (coe v11)))
                (d_distribute_86
                   (coe du_'10214'_'10215''7580'_44 (coe v0)) (coe v10) (coe v11))
                (coe
                   MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                   (coe MAlonzo.Code.Once.CCC.IR.C_id_16)
                   (coe
                      du_elaborate_114 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__142 (coe v10) (coe v11))
                      (coe v13))
                   (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Void_138)
             (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
             (coe
                du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_138)
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v5 v6 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                du_'10214'_'10215''7580'_44
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v8)))
             (coe
                du_elaborate_114
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v8))
                (coe v1) (coe v11))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe MAlonzo.Code.Once.CCC.IR.C_id_16)
                (coe du_elaborate_114 (coe v0) (coe v8) (coe v10))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v5
        -> coe du_intLit_8 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v5
        -> coe du_strLit_14 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v6
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Int_150) d_negIR_28
             (coe
                du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_ltIR_30
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_leIR_32
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_gtIR_34
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_geIR_36
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_eqIR_38
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__140
                (coe MAlonzo.Code.Once.Type.C_Int_150)
                (coe MAlonzo.Code.Once.Type.C_Int_150))
             d_neIR_40
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v7))
                (coe
                   du_elaborate_114 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_150)
                   (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v9)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_54
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_38))
                       (coe v11))
                    (coe MAlonzo.Code.Once.CCC.IR.C_arr_98)
                    (coe
                       du_elaborate_114 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__144 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_54
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_38))
                          (coe v11))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v6
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Unit_136)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_SigOp_156
                (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
                   (coe MAlonzo.Code.Once.Type.C_Unit_136) (coe v1) (coe v6)))
             (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v5
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Unit_136)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_SigOp_156
                (MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'info_356
                   (coe MAlonzo.Code.Once.Type.C_Unit_136) (coe v1) (coe v5)))
             (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
      _ -> MAlonzo.RTE.mazUnreachableError
