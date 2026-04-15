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
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_12
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe MAlonzo.Code.Once.Type.C_Unit_44)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_Prim_156
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.int." :: Data.Text.Text)
            (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v0))))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe MAlonzo.Code.Once.Type.C_Unit_44)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_Prim_156
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.str." :: Data.Text.Text) v0))
      (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_addIR_18
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.add.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_subIR_20
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.sub.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_mulIR_22
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.mul.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_divIR_24
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.div.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_modIR_26
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.mod.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.negIR
d_negIR_28 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_negIR_28
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.neg.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.ltIR
d_ltIR_30 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_ltIR_30
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.lt.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.leIR
d_leIR_32 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_leIR_32
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.le.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.gtIR
d_gtIR_34 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_gtIR_34
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.gt.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.geIR
d_geIR_36 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_geIR_36
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.ge.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.eqIR
d_eqIR_38 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_eqIR_38
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.eq.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.neIR
d_neIR_40 :: MAlonzo.Code.Once.CCC.IR.T_IR_12
d_neIR_40
  = coe
      MAlonzo.Code.Once.CCC.IR.C_Prim_156
      ("arith.ne.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_44 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34
d_'10214'_'10215''7580'_44 ~v0 v1 = du_'10214'_'10215''7580'_44 v1
du_'10214'_'10215''7580'_44 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34
du_'10214'_'10215''7580'_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_44
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__48
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
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
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
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_distribute_86 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe
         MAlonzo.Code.Once.Type.C__'42'__48
         (coe MAlonzo.Code.Once.Type.C__'43'__50 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_104 (coe v0) (coe v1) (coe v2)) (coe du_swap''_78)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryInlSwap_98 v0 v1 ~v2 = du_curryInlSwap_98 v0 v1
du_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_curryInlSwap_98 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_82
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__24
         (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.IR.C_inl_50
            (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryInrSwap_100 v0 ~v1 v2 = du_curryInrSwap_100 v0 v2
du_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
du_curryInrSwap_100 v0 v1
  = coe
      MAlonzo.Code.Once.CCC.IR.C_curry_82
      (coe
         MAlonzo.Code.Once.CCC.IR.C__'8728'__24
         (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.CCC.IR.C_inr_56
            (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_102 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_curryDistrib_102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C_case_64
      (coe du_curryInlSwap_98 (coe v0) (coe v1))
      (coe du_curryInrSwap_100 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_104 ::
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_distrib''_104 v0 v1 v2
  = coe
      MAlonzo.Code.Once.CCC.IR.C__'8728'__24
      (coe
         MAlonzo.Code.Once.Type.C__'42'__48
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v0)
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.C__'43'__50
               (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
         (coe
            MAlonzo.Code.Once.CCC.IR.C__'8728'__24
            (coe MAlonzo.Code.Once.Type.C__'43'__50 (coe v1) (coe v2))
            (d_curryDistrib_102 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.CCC.IR.C_fst_38))
         (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
         (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
-- Once.Surface.Elaborate.elaborate
d_elaborate_112 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_elaborate_112 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v6
        -> coe du_proj_58 (coe v1) (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_curry_82
                    (d_elaborate_112
                       (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v1 v10
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v12) (coe v9))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_194 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v6) (coe v8)
                   (coe v2))
                (coe v6))
             (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v6) (coe v8)
                      (coe v2))
                   (coe v9))
                (d_elaborate_112 (coe v0) (coe v1) (coe v6) (coe v10))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_204 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v6)
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
                (coe v6))
             (coe MAlonzo.Code.Once.CCC.IR.C_apply_90)
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe
                   d_coerceEffToArrow_138 v0 v1 v2 v6 v8 v9
                   (coe du_'10214'_'10215''7580'_44 (coe v1)) v6 v2
                   (d_elaborate_112
                      (coe v0) (coe v1)
                      (coe MAlonzo.Code.Once.Type.C_Eff_54 (coe v6) (coe v2)) (coe v8)))
                (d_elaborate_112 (coe v0) (coe v1) (coe v6) (coe v9))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_214 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__48 v10 v11
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                    (d_elaborate_112 (coe v0) (coe v1) (coe v10) (coe v8))
                    (d_elaborate_112 (coe v0) (coe v1) (coe v11) (coe v9))
                    (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_224 v7 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v2) (coe v7))
             (coe MAlonzo.Code.Once.CCC.IR.C_fst_38)
             (d_elaborate_112
                (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v2) (coe v7))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_234 v6 v8
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v6) (coe v2))
             (coe MAlonzo.Code.Once.CCC.IR.C_snd_44)
             (d_elaborate_112
                (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__48 (coe v6) (coe v2))
                (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_244 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__50 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v9
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_inl_50
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
                    (d_elaborate_112 (coe v0) (coe v1) (coe v9) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_254 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__50 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24 v10
                    (coe
                       MAlonzo.Code.Once.CCC.IR.C_inr_56
                       (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
                    (d_elaborate_112 (coe v0) (coe v1) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_266 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'43'__50
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v6)))
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v7))))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_case_64
                (d_elaborate_112
                   (coe addInt (coe (1 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v6))
                   (coe v2) (coe v10))
                (d_elaborate_112
                   (coe addInt (coe (1 :: Integer)) (coe v0))
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v7))
                   (coe v2) (coe v11)))
             (coe
                MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__48
                   (coe du_'10214'_'10215''7580'_44 (coe v1))
                   (coe MAlonzo.Code.Once.Type.C__'43'__50 (coe v6) (coe v7)))
                (d_distribute_86
                   (coe du_'10214'_'10215''7580'_44 (coe v1)) (coe v6) (coe v7))
                (coe
                   MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                   (coe MAlonzo.Code.Once.CCC.IR.C_id_16)
                   (d_elaborate_112
                      (coe v0) (coe v1)
                      (coe MAlonzo.Code.Once.Type.C__'43'__50 (coe v6) (coe v7))
                      (coe v9))
                   (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10)))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_272
        -> coe MAlonzo.Code.Once.CCC.IR.C_terminal_68
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_280 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Void_46)
             (coe MAlonzo.Code.Once.CCC.IR.C_initial_72)
             (d_elaborate_112
                (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_46) (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_290 v6 v8 v9
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                du_'10214'_'10215''7580'_44
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v6)))
             (d_elaborate_112
                (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v6))
                (coe v2) (coe v9))
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (coe MAlonzo.Code.Once.CCC.IR.C_id_16)
                (d_elaborate_112 (coe v0) (coe v1) (coe v6) (coe v8))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_int_296 v6
        -> coe du_intLit_8 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_str_302 v6
        -> coe du_strLit_14 (coe v6)
      MAlonzo.Code.Once.Surface.Syntax.C_add_308 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_314 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_320 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_div_326 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_332 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_338 v6
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Int_60) d_negIR_28
             (d_elaborate_112
                (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_344 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_ltIR_30
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_le_350 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_leIR_32
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_356 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_gtIR_34
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_362 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_geIR_36
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_368 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_eqIR_38
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_374 v6 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe
                MAlonzo.Code.Once.Type.C__'42'__48
                (coe MAlonzo.Code.Once.Type.C_Int_60)
                (coe MAlonzo.Code.Once.Type.C_Int_60))
             d_neIR_40
             (coe
                MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_32
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v6))
                (d_elaborate_112
                   (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Int_60) (coe v7))
                (coe MAlonzo.Code.Once.CCC.IR.C_Heap_10))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_384 v8
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C_Eff_54 v9 v10
               -> coe
                    MAlonzo.Code.Once.CCC.IR.C__'8728'__24
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v9)
                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))
                    (coe MAlonzo.Code.Once.CCC.IR.C_arr_98)
                    (d_elaborate_112
                       (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__52 (coe v9)
                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_prim_392 v7
        -> coe
             MAlonzo.Code.Once.CCC.IR.C__'8728'__24
             (coe MAlonzo.Code.Once.Type.C_Unit_44)
             (coe MAlonzo.Code.Once.CCC.IR.C_Prim_156 v7)
             (coe MAlonzo.Code.Once.CCC.IR.C_terminal_68)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate._.coerceEffToArrow
d_coerceEffToArrow_138 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.Type.T_Type_34 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_12
d_coerceEffToArrow_138 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe d_unsafeCoerce_150 v0 v1 v2 v3 v4 v5 v6 v7 v8 v6 v7 v8
-- Once.Surface.Elaborate._._.unsafeCoerce
d_unsafeCoerce_150
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Surface.Elaborate._._.unsafeCoerce"
