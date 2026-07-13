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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 -> MAlonzo.Code.Once.IR.T_IR_16
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.IR.T_IR_16
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.IR.C_const_160
         (coe MAlonzo.Code.Once.Type.C_fits'45'int_198)
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> MAlonzo.Code.Once.IR.T_IR_16
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.IR.C_SigOp_166
         (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_190
            (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.IR.T_IR_16
d_addIR_18
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_166
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.IR.T_IR_16
d_subIR_20
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_168
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.IR.T_IR_16
d_mulIR_22
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_170
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.IR.T_IR_16
d_divIR_24
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_172
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.IR.T_IR_16
d_modIR_26
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_174
-- Once.Surface.Elaborate.negIR
d_negIR_28 :: MAlonzo.Code.Once.IR.T_IR_16
d_negIR_28
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_176
-- Once.Surface.Elaborate.ltIR
d_ltIR_30 :: MAlonzo.Code.Once.IR.T_IR_16
d_ltIR_30
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_178
-- Once.Surface.Elaborate.leIR
d_leIR_32 :: MAlonzo.Code.Once.IR.T_IR_16
d_leIR_32
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_180
-- Once.Surface.Elaborate.gtIR
d_gtIR_34 :: MAlonzo.Code.Once.IR.T_IR_16
d_gtIR_34
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_182
-- Once.Surface.Elaborate.geIR
d_geIR_36 :: MAlonzo.Code.Once.IR.T_IR_16
d_geIR_36
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_184
-- Once.Surface.Elaborate.eqIR
d_eqIR_38 :: MAlonzo.Code.Once.IR.T_IR_16
d_eqIR_38
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_186
-- Once.Surface.Elaborate.neIR
d_neIR_40 :: MAlonzo.Code.Once.IR.T_IR_16
d_neIR_40
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_166
      MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_188
-- Once.Surface.Elaborate.proj
d_proj_48 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_proj_48 ~v0 v1 v2 = du_proj_48 v1 v2
du_proj_48 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_proj_48 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_50
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                       (coe v3))
                    (coe du_proj_48 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_68 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swap''_68 ~v0 ~v1 v2 = du_swap''_68 v2
du_swap''_68 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_swap''_68 v0
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
      (coe MAlonzo.Code.Once.IR.C_snd_50)
      (coe MAlonzo.Code.Once.IR.C_fst_44) v0
-- Once.Surface.Elaborate.distribute
d_distribute_78 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_98 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_swap''_68 (coe v3))
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_92 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInlSwap_92 v0 v1 ~v2 v3 = du_curryInlSwap_92 v0 v1 v3
du_curryInlSwap_92 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInlSwap_92 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_88
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_56 v2) (coe du_swap''_68 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_94 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInrSwap_94 v0 ~v1 v2 v3 = du_curryInrSwap_94 v0 v2 v3
du_curryInrSwap_94 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInrSwap_94 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_88
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_62 v2) (coe du_swap''_68 (coe v2)))
      v2
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_96 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryDistrib_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C_case_70
      (coe du_curryInlSwap_92 (coe v0) (coe v1) (coe v3))
      (coe du_curryInrSwap_94 (coe v0) (coe v2) (coe v3))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_98 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distrib''_98 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.Type.C__'42'__126
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_pure_34))
            (coe
               MAlonzo.Code.Once.Type.C__'43'__128
               (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_96)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v1) (coe v2))
            (d_curryDistrib_96 (coe v0) (coe v1) (coe v2) (coe v3))
            (coe MAlonzo.Code.Once.IR.C_fst_44))
         (coe MAlonzo.Code.Once.IR.C_snd_50) v3)
-- Once.Surface.Elaborate.elaborate
d_elaborate_108 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate_108 ~v0 v1 ~v2 v3 v4 v5 = du_elaborate_108 v1 v3 v4 v5
du_elaborate_108 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate_108 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v6
        -> coe du_proj_48 (coe v0) (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v7 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_88
                    (coe
                       du_elaborate_108
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v13
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v15) (coe v2) (coe v12))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v6 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v8))
             (coe MAlonzo.Code.Once.IR.C_apply_96)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                      (coe v1))
                   (coe v2) (coe v11))
                (coe du_elaborate_108 (coe v0) (coe v8) (coe v2) (coe v12)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v6 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                       (coe MAlonzo.Code.Once.Type.C_Unit_122)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v14))
                    (coe MAlonzo.Code.Once.IR.C_arr_104)
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_88
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                             (coe v0))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__30
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__126
                                (coe
                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                   (coe MAlonzo.Code.Once.Type.d_effK_62) (coe v14))
                                (coe v8))
                             (coe MAlonzo.Code.Once.IR.C_apply_96)
                             (coe
                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                (coe
                                   du_elaborate_108 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                      (coe MAlonzo.Code.Once.Type.d_effK_62) (coe v14))
                                   (coe v2) (coe v10))
                                (coe du_elaborate_108 (coe v0) (coe v8) (coe v2) (coe v11)) v2))
                          (coe MAlonzo.Code.Once.IR.C_fst_44))
                       v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v6 v7 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe du_elaborate_108 (coe v0) (coe v12) (coe v2) (coe v10))
                    (coe du_elaborate_108 (coe v0) (coe v13) (coe v2) (coe v11)) v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v8))
             (coe MAlonzo.Code.Once.IR.C_fst_44)
             (coe
                du_elaborate_108 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v8))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v7 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_50)
             (coe
                du_elaborate_108 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v1))
                (coe v2) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30 v10
                    (coe MAlonzo.Code.Once.IR.C_inl_56 v2)
                    (coe du_elaborate_108 (coe v0) (coe v10) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30 v11
                    (coe MAlonzo.Code.Once.IR.C_inr_62 v2)
                    (coe du_elaborate_108 (coe v0) (coe v11) (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'43'__128
                (coe
                   MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v11)))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0)
                      (coe v12))))
             (coe
                MAlonzo.Code.Once.IR.C_case_70
                (coe
                   du_elaborate_108
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v11))
                   (coe v1) (coe v2) (coe v15))
                (coe
                   du_elaborate_108
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v12))
                   (coe v1) (coe v2) (coe v16)))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__126
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                      (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v11) (coe v12)))
                (d_distribute_78
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                      (coe v0))
                   (coe v11) (coe v12) (coe v2))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                   (coe MAlonzo.Code.Once.IR.C_id_22)
                   (coe
                      du_elaborate_108 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v11) (coe v12))
                      (coe v2) (coe v14))
                   v2))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C_Void_124)
             (coe MAlonzo.Code.Once.IR.C_initial_78)
             (coe
                du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_124)
                (coe v2) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v6 v7 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v9)))
             (coe
                du_elaborate_108
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v9))
                (coe v1) (coe v2) (coe v12))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe MAlonzo.Code.Once.IR.C_id_22)
                (coe du_elaborate_108 (coe v0) (coe v9) (coe v2) (coe v11)) v2)
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v6
        -> coe du_intLit_8 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v6
        -> coe du_strLit_14 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_add_200 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_sub_210 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mul_220 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_div_230 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_240 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_neg_248 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C_Int_136) d_negIR_28
             (coe
                du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe v2) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_258 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_ltIR_30
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_le_268 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_leIR_32
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_gt_278 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_gtIR_34
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ge_288 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_geIR_36
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_eq_298 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_eqIR_38
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_ne_308 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.Type.C__'42'__126
                (coe MAlonzo.Code.Once.Type.C_Int_136)
                (coe MAlonzo.Code.Once.Type.C_Int_136))
             d_neIR_40
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v8))
                (coe
                   du_elaborate_108 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_136)
                   (coe v2) (coe v9))
                v2)
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_320 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v12))
                    (coe MAlonzo.Code.Once.IR.C_arr_104)
                    (coe
                       du_elaborate_108 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v12))
                       (coe v2) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_328 v7 v8
        -> let v9
                 = coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.IR.C_SigOp_166
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_204
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7)
                           (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_150)
                           (coe v8)))
                     (coe MAlonzo.Code.Once.IR.C_terminal_74) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                  -> case coe v8 of
                       MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_186 v16 v17
                         -> coe
                              MAlonzo.Code.Once.IR.C_curry_88
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30 v10
                                 (coe
                                    MAlonzo.Code.Once.IR.C_SigOp_166
                                    (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_246
                                       (coe v10) (coe v12) (coe v11) (coe v7) (coe v16) (coe v17)))
                                 (coe MAlonzo.Code.Once.IR.C_snd_50))
                              v2
                       _ -> coe v9
                _ -> coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_336 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C_Unit_122)
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_166
                (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_214
                   (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_346 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.Type.C_Unit_122)
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_166
                (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_214
                   (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v6))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_358 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_88
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30 v10 v9
                       (coe MAlonzo.Code.Once.IR.C_snd_50))
                    v2
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_370 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9
             (coe du_elaborate_108 (coe v0) (coe v7) (coe v2) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_382 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> coe
                                  MAlonzo.Code.Once.IR.C_curry_88
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30 v11
                                     (coe
                                        MAlonzo.Code.Once.IR.C_Cata_118 v9
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__30
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__126
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                 (coe
                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                    (coe v14) (coe v13))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v16))
                                                 (coe v13))
                                              (coe
                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                 (coe v14) (coe v13)))
                                           (coe MAlonzo.Code.Once.IR.C_apply_96)
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                              (coe
                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8))
                                                 (coe
                                                    du_elaborate_108
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                          (coe v14) (coe v13))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v16))
                                                       (coe v13))
                                                    (coe v2) (coe v10))
                                                 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                              (coe MAlonzo.Code.Once.IR.C_id_22) v2)))
                                     (coe MAlonzo.Code.Once.IR.C_snd_50))
                                  v2
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_394 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v16
                             -> coe
                                  MAlonzo.Code.Once.IR.C_curry_88
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30 v11
                                     (coe
                                        MAlonzo.Code.Once.IR.C_Ana_138 v9
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__30
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'42'__126
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                 (coe v11)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v15))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                    (coe v16) (coe v11)))
                                              (coe v11))
                                           (coe MAlonzo.Code.Once.IR.C_apply_96)
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                              (coe
                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8))
                                                 (coe
                                                    du_elaborate_108
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                       (coe v11)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v15))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                          (coe v16) (coe v11)))
                                                    (coe v2) (coe v10))
                                                 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                              (coe MAlonzo.Code.Once.IR.C_id_22) v2)))
                                     (coe MAlonzo.Code.Once.IR.C_snd_50))
                                  v2
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_318 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate'45'default_318 ~v0 v1 ~v2 v3
  = du_elaborate'45'default_318 v1 v3
du_elaborate'45'default_318 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate'45'default_318 v0 v1
  = coe
      du_elaborate_108 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Surface.Elaborate.distribute-default
d_distribute'45'default_326 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute'45'default_326 v0 v1 v2
  = coe
      d_distribute_78 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
