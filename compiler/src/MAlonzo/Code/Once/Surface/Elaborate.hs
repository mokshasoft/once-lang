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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Postulates
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.IR.T_IR_10
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__22
      (coe MAlonzo.Code.Once.Type.C_Unit_34)
      (coe
         MAlonzo.Code.Once.IR.C_Prim_104
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.int." :: Data.Text.Text)
            (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v0))))
      (coe MAlonzo.Code.Once.IR.C_terminal_66)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__22
      (coe MAlonzo.Code.Once.Type.C_Unit_34)
      (coe
         MAlonzo.Code.Once.IR.C_Prim_104
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("lit.str." :: Data.Text.Text) v0))
      (coe MAlonzo.Code.Once.IR.C_terminal_66)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.IR.T_IR_10
d_addIR_18
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.add.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.IR.T_IR_10
d_subIR_20
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.sub.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.IR.T_IR_10
d_mulIR_22
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.mul.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.IR.T_IR_10
d_divIR_24
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.div.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.IR.T_IR_10
d_modIR_26
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.mod.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.negIR
d_negIR_28 :: MAlonzo.Code.Once.IR.T_IR_10
d_negIR_28
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.neg.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.ltIR
d_ltIR_30 :: MAlonzo.Code.Once.IR.T_IR_10
d_ltIR_30
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.lt.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.leIR
d_leIR_32 :: MAlonzo.Code.Once.IR.T_IR_10
d_leIR_32
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.le.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.gtIR
d_gtIR_34 :: MAlonzo.Code.Once.IR.T_IR_10
d_gtIR_34
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.gt.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.geIR
d_geIR_36 :: MAlonzo.Code.Once.IR.T_IR_10
d_geIR_36
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.ge.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.eqIR
d_eqIR_38 :: MAlonzo.Code.Once.IR.T_IR_10
d_eqIR_38
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.eq.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.neIR
d_neIR_40 :: MAlonzo.Code.Once.IR.T_IR_10
d_neIR_40
  = coe
      MAlonzo.Code.Once.IR.C_Prim_104 ("arith.ne.int" :: Data.Text.Text)
-- Once.Surface.Elaborate.⟦_⟧ᶜ
d_'10214'_'10215''7580'_44 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32
d_'10214'_'10215''7580'_44 ~v0 v1 = du_'10214'_'10215''7580'_44 v1
du_'10214'_'10215''7580'_44 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32
du_'10214'_'10215''7580'_44 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
        -> coe MAlonzo.Code.Once.Type.C_Unit_34
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Type.C__'42'__38
             (coe du_'10214'_'10215''7580'_44 (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.proj
d_proj_58 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_10
d_proj_58 ~v0 v1 v2 = du_proj_58 v1 v2
du_proj_58 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_10
du_proj_58 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_34
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__22
                    (coe du_'10214'_'10215''7580'_44 (coe v3))
                    (coe du_proj_58 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_28)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_78 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_swap''_78 ~v0 ~v1 = du_swap''_78
du_swap''_78 :: MAlonzo.Code.Once.IR.T_IR_10
du_swap''_78
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
      (coe MAlonzo.Code.Once.IR.C_snd_34)
      (coe MAlonzo.Code.Once.IR.C_fst_28)
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Surface.Elaborate.distribute
d_distribute_86 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_distribute_86 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__22
      (coe
         MAlonzo.Code.Once.Type.C__'42'__38
         (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v2))
         (coe v0))
      (d_distrib''_104 (coe v0) (coe v1) (coe v2)) (coe du_swap''_78)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_curryInlSwap_98 v0 v1 ~v2 = du_curryInlSwap_98 v0 v1
du_curryInlSwap_98 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
du_curryInlSwap_98 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_78
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__22
         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.IR.C_inl_48 (coe MAlonzo.Code.Once.IR.C_Heap_8))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_curryInrSwap_100 v0 ~v1 v2 = du_curryInrSwap_100 v0 v2
du_curryInrSwap_100 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
du_curryInrSwap_100 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_78
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__22
         (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.IR.C_inr_54 (coe MAlonzo.Code.Once.IR.C_Heap_8))
         (coe du_swap''_78))
      (coe MAlonzo.Code.Once.IR.C_Heap_8)
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_102 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_curryDistrib_102 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62
      (coe du_curryInlSwap_98 (coe v0) (coe v1))
      (coe du_curryInrSwap_100 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_104 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 -> MAlonzo.Code.Once.IR.T_IR_10
d_distrib''_104 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__22
      (coe
         MAlonzo.Code.Once.Type.C__'42'__38
         (coe
            MAlonzo.Code.Once.Type.d__'8658'__64 (coe v0)
            (coe
               MAlonzo.Code.Once.Type.C__'43'__40
               (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_84)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__22
            (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v1) (coe v2))
            (d_curryDistrib_102 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_28))
         (coe MAlonzo.Code.Once.IR.C_snd_34)
         (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.Surface.Elaborate.elaborate
d_elaborate_112 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_elaborate_112 ~v0 v1 v2 v3 = du_elaborate_112 v1 v2 v3
du_elaborate_112 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_162 ->
  MAlonzo.Code.Once.IR.T_IR_10
du_elaborate_112 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_170 v5
        -> coe du_proj_58 (coe v0) (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_182 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Postulates.d_coerceIRArrow_38
                    (coe du_'10214'_'10215''7580'_44 (coe v0)) v9 v11
                    (coe MAlonzo.Code.Once.Type.C_Many_10) v10
                    (coe
                       MAlonzo.Code.Once.IR.C_curry_78
                       (coe
                          du_elaborate_112
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v0 v9
                             (coe MAlonzo.Code.Once.Type.C_Many_10))
                          (coe v11) (coe v8))
                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_194 v5 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v5) (coe v1))
                (coe v5))
             (coe MAlonzo.Code.Once.IR.C_apply_84)
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   MAlonzo.Code.Once.Postulates.d_coerceIRArrow_38
                   (coe du_'10214'_'10215''7580'_44 (coe v0)) v5 v1 v7
                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                   (coe
                      du_elaborate_112 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__42 (coe v5) (coe v7)
                         (coe v1))
                      (coe v8)))
                (coe du_elaborate_112 (coe v0) (coe v5) (coe v9))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_pair_204 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__38 v9 v10
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                    (coe du_elaborate_112 (coe v0) (coe v9) (coe v7))
                    (coe du_elaborate_112 (coe v0) (coe v10) (coe v8))
                    (coe MAlonzo.Code.Once.IR.C_Heap_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_214 v6 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v6))
             (coe MAlonzo.Code.Once.IR.C_fst_28)
             (coe
                du_elaborate_112 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v1) (coe v6))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_224 v5 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v1))
             (coe MAlonzo.Code.Once.IR.C_snd_34)
             (coe
                du_elaborate_112 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__38 (coe v5) (coe v1))
                (coe v7))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_234 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__22 v8
                    (coe
                       MAlonzo.Code.Once.IR.C_inl_48 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                    (coe du_elaborate_112 (coe v0) (coe v8) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_244 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__40 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__22 v9
                    (coe
                       MAlonzo.Code.Once.IR.C_inr_54 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                    (coe du_elaborate_112 (coe v0) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_256 v5 v6 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'43'__40
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5)))
                (coe
                   du_'10214'_'10215''7580'_44
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v6))))
             (coe
                MAlonzo.Code.Once.IR.C_'91'_'44'_'93'_62
                (coe
                   du_elaborate_112
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5))
                   (coe v1) (coe v9))
                (coe
                   du_elaborate_112
                   (coe
                      MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v6))
                   (coe v1) (coe v10)))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__22
                (coe
                   MAlonzo.Code.Once.Type.C__'42'__38
                   (coe du_'10214'_'10215''7580'_44 (coe v0))
                   (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v5) (coe v6)))
                (d_distribute_86
                   (coe du_'10214'_'10215''7580'_44 (coe v0)) (coe v5) (coe v6))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                   (coe MAlonzo.Code.Once.IR.C_id_14)
                   (coe
                      du_elaborate_112 (coe v0)
                      (coe MAlonzo.Code.Once.Type.C__'43'__40 (coe v5) (coe v6))
                      (coe v8))
                   (coe MAlonzo.Code.Once.IR.C_Heap_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_262
        -> coe MAlonzo.Code.Once.IR.C_terminal_66
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_270 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C_Void_36)
             (coe MAlonzo.Code.Once.IR.C_initial_70)
             (coe
                du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Void_36)
                (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_280 v5 v7 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                du_'10214'_'10215''7580'_44
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5)))
             (coe
                du_elaborate_112
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v5))
                (coe v1) (coe v8))
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe MAlonzo.Code.Once.IR.C_id_14)
                (coe du_elaborate_112 (coe v0) (coe v5) (coe v7))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_int_286 v5
        -> coe du_intLit_8 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_str_292 v5
        -> coe du_strLit_14 (coe v5)
      MAlonzo.Code.Once.Surface.Syntax.C_add_298 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_304 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_310 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_316 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_322 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_328 v5
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C_Int_48) d_negIR_28
             (coe
                du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe v5))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_334 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_ltIR_30
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_le_340 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_leIR_32
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_346 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_gtIR_34
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_352 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_geIR_36
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_358 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_eqIR_38
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v5 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe
                MAlonzo.Code.Once.Type.C__'42'__38
                (coe MAlonzo.Code.Once.Type.C_Int_48)
                (coe MAlonzo.Code.Once.Type.C_Int_48))
             d_neIR_40
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_42
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v5))
                (coe
                   du_elaborate_112 (coe v0) (coe MAlonzo.Code.Once.Type.C_Int_48)
                   (coe v6))
                (coe MAlonzo.Code.Once.IR.C_Heap_8))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_374 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Eff_44 v8 v9
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__22
                    (MAlonzo.Code.Once.Type.d__'8658'__64 (coe v8) (coe v9))
                    (coe MAlonzo.Code.Once.IR.C_arr_98)
                    (coe
                       du_elaborate_112 (coe v0)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__64 (coe v8) (coe v9))
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_roll''_382 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Fix_46 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__22 v7
                    (coe MAlonzo.Code.Once.IR.C_fold_88)
                    (coe du_elaborate_112 (coe v0) (coe v7) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unroll''_390 v6
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__22
             (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1))
             (coe MAlonzo.Code.Once.IR.C_unfold_92)
             (coe
                du_elaborate_112 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Fix_46 (coe v1)) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
