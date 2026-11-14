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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.CoerceIR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Concrete

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.IR.T_IR_16
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_134
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'int_516) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.Surface.Elaborate.floatLit
d_floatLit_14 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_floatLit_14 v0 ~v1 = du_floatLit_14 v0
du_floatLit_14 ::
  MAlonzo.Code.Once.Spec.Float.Decimal.T_Decimal_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_floatLit_14 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_134
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'float_518) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.IR.T_IR_16
d_addIR_18
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.IR.T_IR_16
d_subIR_20
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.IR.T_IR_16
d_mulIR_22
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.IR.T_IR_16
d_divIR_24
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.IR.T_IR_16
d_modIR_26
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
-- Once.Surface.Elaborate.faddIR
d_faddIR_28 :: MAlonzo.Code.Once.IR.T_IR_16
d_faddIR_28
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34))
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
-- Once.Surface.Elaborate.fsubIR
d_fsubIR_30 :: MAlonzo.Code.Once.IR.T_IR_16
d_fsubIR_30
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34))
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
-- Once.Surface.Elaborate.fmulIR
d_fmulIR_32 :: MAlonzo.Code.Once.IR.T_IR_16
d_fmulIR_32
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34))
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
-- Once.Surface.Elaborate.fdivIR
d_fdivIR_34 :: MAlonzo.Code.Once.IR.T_IR_16
d_fdivIR_34
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
         (coe MAlonzo.Code.Once.Spec.Type.C_Float_34))
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
-- Once.Surface.Elaborate.i2fIR
d_i2fIR_36 :: MAlonzo.Code.Once.IR.T_IR_16
d_i2fIR_36
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Spec.Type.C_Float_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136)
-- Once.Surface.Elaborate.negIR
d_negIR_38 :: MAlonzo.Code.Once.IR.T_IR_16
d_negIR_38
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124)
-- Once.Surface.Elaborate.ltIR
d_ltIR_40 :: MAlonzo.Code.Once.IR.T_IR_16
d_ltIR_40
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_196)
-- Once.Surface.Elaborate.leIR
d_leIR_42 :: MAlonzo.Code.Once.IR.T_IR_16
d_leIR_42
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_198)
-- Once.Surface.Elaborate.gtIR
d_gtIR_44 :: MAlonzo.Code.Once.IR.T_IR_16
d_gtIR_44
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_200)
-- Once.Surface.Elaborate.geIR
d_geIR_46 :: MAlonzo.Code.Once.IR.T_IR_16
d_geIR_46
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_202)
-- Once.Surface.Elaborate.eqIR
d_eqIR_48 :: MAlonzo.Code.Once.IR.T_IR_16
d_eqIR_48
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_204)
-- Once.Surface.Elaborate.neIR
d_neIR_50 :: MAlonzo.Code.Once.IR.T_IR_16
d_neIR_50
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_140
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'42'__22
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32)
         (coe MAlonzo.Code.Once.Spec.Type.C_Int_32))
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'43'__24
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_206)
-- Once.Surface.Elaborate.numIR
d_numIR_60 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Theory_16 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_numIR_60 ~v0 v1 ~v2 v3 v4 v5 = du_numIR_60 v1 v3 v4 v5
du_numIR_60 ::
  MAlonzo.Code.Once.Spec.Theory.T_NumTy_6 ->
  MAlonzo.Code.Once.Spec.Theory.T_Shape_30 ->
  MAlonzo.Code.Once.Spec.Theory.T_Has_104 ->
  MAlonzo.Code.Once.Spec.Theory.T_Sym_38 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_numIR_60 v0 v1 v2 v3
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Once.IR.C_SigOp_140
            (coe MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v0) (coe v1))
            (coe MAlonzo.Code.Once.Spec.Theory.du_symCod_90 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Arith.SigOp.Builders.du_numInfo_186 (coe v0)
               (coe v1) (coe v2) (coe v3))))
-- Once.Surface.Elaborate.proj
d_proj_94 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_proj_94 v0 ~v1 v2 v3 = du_proj_94 v0 v2 v3
du_proj_94 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_proj_94 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_48
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v4)))
                    (coe du_proj_94 (coe v0) (coe v4) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.restrictEnv
d_restrictEnv_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_restrictEnv_118 v0 ~v1 v2 v3 v4 ~v5 v6
  = du_restrictEnv_118 v0 v2 v3 v4 v6
du_restrictEnv_118 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__84 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_restrictEnv_118 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v4) (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v6 v7
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Context.C__'8849''8759'__98 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v16 v17
                      -> case coe v3 of
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v19 v20
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> case coe v13 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                (coe v20) (coe v14)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> case coe v13 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                MAlonzo.Code.Once.IR.C__'8728'__28
                                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du__'8638'__64
                                                         (coe v6) (coe v17))))
                                                (coe
                                                   du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                   (coe v20) (coe v14))
                                                (coe MAlonzo.Code.Once.IR.C_fst_42)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> case coe v13 of
                                         MAlonzo.Code.Once.Spec.Grade.C_0'8804'q_26
                                           -> coe
                                                MAlonzo.Code.Once.IR.C__'8728'__28
                                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                   (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du__'8638'__64
                                                         (coe v6) (coe v17))))
                                                (coe
                                                   du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                   (coe v20) (coe v14))
                                                (coe MAlonzo.Code.Once.IR.C_fst_42)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'1_28
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_1'8804'ω_30
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         MAlonzo.Code.Once.Spec.Grade.C_ω'8804'ω_32
                                           -> coe
                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                                (coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                         (coe
                                                            MAlonzo.Code.Once.Context.du__'8638'__64
                                                            (coe v6) (coe v17))))
                                                   (coe
                                                      du_restrictEnv_118 (coe v0) (coe v6) (coe v17)
                                                      (coe v20) (coe v14))
                                                   (coe MAlonzo.Code.Once.IR.C_fst_42))
                                                (coe MAlonzo.Code.Once.IR.C_snd_48)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.projUsed
d_projUsed_178 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_projUsed_178 ~v0 ~v1 v2 v3 = du_projUsed_178 v2 v3
du_projUsed_178 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_projUsed_178 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_48
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_projUsed_178 (coe v3) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.envˡ
d_env'737'_202 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'737'_202 v0 ~v1 v2 ~v3 v4 v5 = du_env'737'_202 v0 v2 v4 v5
du_env'737'_202 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'737'_202 v0 v1 v2 v3
  = coe
      du_restrictEnv_118 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
         (coe v3))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v2)
         (coe v3))
-- Once.Surface.Elaborate.envʳ
d_env'691'_224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'691'_224 v0 ~v1 v2 ~v3 v4 v5 = du_env'691'_224 v0 v2 v4 v5
du_env'691'_224 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'691'_224 v0 v1 v2 v3
  = coe
      du_restrictEnv_118 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
         (coe v3))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142 (coe v2)
         (coe v3))
-- Once.Surface.Elaborate.envʳω
d_env'691'ω_246 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'691'ω_246 v0 ~v1 v2 ~v3 v4 v5 = du_env'691'ω_246 v0 v2 v4 v5
du_env'691'ω_246 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'691'ω_246 v0 v1 v2 v3
  = coe
      du_restrictEnv_118 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v3)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3)))
         (coe
            MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206 (coe v3))
         (coe
            MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142 (coe v2)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
               (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v3))))
-- Once.Surface.Elaborate.bindEnv
d_bindEnv_270 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_bindEnv_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_bindEnv_270 v6
du_bindEnv_270 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_bindEnv_270 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe MAlonzo.Code.Once.IR.C_id_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_288 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swap''_288 ~v0 ~v1 ~v2 = du_swap''_288
du_swap''_288 :: MAlonzo.Code.Once.IR.T_IR_16
du_swap''_288
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
      (coe MAlonzo.Code.Once.IR.C_snd_48)
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Surface.Elaborate.distribute
d_distribute_298 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute_298 v0 v1 v2 ~v3 = du_distribute_298 v0 v1 v2
du_distribute_298 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribute_298 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
         (coe v0))
      (coe du_distrib''_318 (coe v0) (coe v1) (coe v2))
      (coe du_swap''_288)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_312 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInlSwap_312 v0 v1 ~v2 ~v3 = du_curryInlSwap_312 v0 v1
du_curryInlSwap_312 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInlSwap_312 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swap''_288))
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_314 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInrSwap_314 v0 ~v1 v2 ~v3 = du_curryInrSwap_314 v0 v2
du_curryInrSwap_314 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInrSwap_314 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_60) (coe du_swap''_288))
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_316 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryDistrib_316 v0 v1 v2 ~v3 = du_curryDistrib_316 v0 v1 v2
du_curryDistrib_316 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryDistrib_316 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_case_68
      (coe du_curryInlSwap_312 (coe v0) (coe v1))
      (coe du_curryInrSwap_314 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_318 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distrib''_318 v0 v1 v2 ~v3 = du_distrib''_318 v0 v1 v2
du_distrib''_318 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distrib''_318 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
            (coe du_curryDistrib_316 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Surface.Elaborate.swapIR
d_swapIR_324 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swapIR_324 ~v0 ~v1 ~v2 = du_swapIR_324
du_swapIR_324 :: MAlonzo.Code.Once.IR.T_IR_16
du_swapIR_324
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
      (coe MAlonzo.Code.Once.IR.C_snd_48)
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Surface.Elaborate.distribIR
d_distribIR_336 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribIR_336 v0 v1 v2 ~v3 = du_distribIR_336 v0 v1 v2
du_distribIR_336 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribIR_336 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_90)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Once.IR.C_case_68
               (coe
                  MAlonzo.Code.Once.IR.C_curry_84
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swapIR_324)))
               (coe
                  MAlonzo.Code.Once.IR.C_curry_84
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))
                     (coe MAlonzo.Code.Once.IR.C_inr_60) (coe du_swapIR_324))))
            (coe MAlonzo.Code.Once.IR.C_snd_48))
         (coe MAlonzo.Code.Once.IR.C_fst_42))
-- Once.Surface.Elaborate.compIR
d_compIR_348 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_compIR_348 v0 v1 v2 ~v3 = du_compIR_348 v0 v1 v2
du_compIR_348 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_compIR_348 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
            (coe v1))
         (coe MAlonzo.Code.Once.IR.C_apply_90)
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_fst_42))
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                  (coe v0))
               (coe MAlonzo.Code.Once.IR.C_apply_90)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1)))
                     (coe MAlonzo.Code.Once.IR.C_snd_48)
                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                  (coe MAlonzo.Code.Once.IR.C_snd_48)))))
-- Once.Surface.Elaborate.copairIR
d_copairIR_360 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_copairIR_360 v0 v1 v2 ~v3 = du_copairIR_360 v0 v1 v2
du_copairIR_360 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_copairIR_360 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe
            MAlonzo.Code.Once.IRTy.C__'43'__22
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
               (coe v0))
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
               (coe v1)))
         (coe
            MAlonzo.Code.Once.IR.C_case_68
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                  (coe v0))
               (coe MAlonzo.Code.Once.IR.C_apply_90)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
                     (coe MAlonzo.Code.Once.IR.C_fst_42)
                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                  (coe MAlonzo.Code.Once.IR.C_snd_48)))
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__28
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                  (coe v1))
               (coe MAlonzo.Code.Once.IR.C_apply_90)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
                     (coe MAlonzo.Code.Once.IR.C_snd_48)
                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                  (coe MAlonzo.Code.Once.IR.C_snd_48))))
         (coe
            du_distribIR_336
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
            (coe v0) (coe v1)))
-- Once.Surface.Elaborate.forkIR
d_forkIR_372 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_forkIR_372 v0 v1 v2 ~v3 = du_forkIR_372 v0 v1 v2
du_forkIR_372 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_forkIR_372 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
               (coe v0))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2)))
                  (coe MAlonzo.Code.Once.IR.C_fst_42)
                  (coe MAlonzo.Code.Once.IR.C_fst_42))
               (coe MAlonzo.Code.Once.IR.C_snd_48)))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe v0))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2)))
                  (coe MAlonzo.Code.Once.IR.C_snd_48)
                  (coe MAlonzo.Code.Once.IR.C_fst_42))
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.curryIR
d_curryIR_384 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryIR_384 v0 v1 v2 ~v3 = du_curryIR_384 v0 v1 v2
du_curryIR_384 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryIR_384 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_curry_84
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                  (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__28
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                        (coe v2))
                     (coe v0))
                  (coe MAlonzo.Code.Once.IR.C_fst_42)
                  (coe MAlonzo.Code.Once.IR.C_fst_42))
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'8667'__24
                           (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                           (coe v2))
                        (coe v0))
                     (coe MAlonzo.Code.Once.IR.C_snd_48)
                     (coe MAlonzo.Code.Once.IR.C_fst_42))
                  (coe MAlonzo.Code.Once.IR.C_snd_48)))))
-- Once.Surface.Elaborate.cataM
d_cataM_396 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_cataM_396 v0 ~v1 v2 v3 v4 ~v5 = du_cataM_396 v0 v2 v3 v4
du_cataM_396 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_cataM_396 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_Cata_106
         (coe
            MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v1)
            (coe v3))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v1)
                        (coe v2)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v2)))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v1)
                     (coe v2))))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.anaM
d_anaM_418 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_anaM_418 v0 ~v1 v2 v3 ~v4 v5 ~v6 = du_anaM_418 v0 v2 v3 v5
du_anaM_418 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_anaM_418 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_Ana_122
         (coe
            MAlonzo.Code.Once.IRTy.WF.du_wf'45''8970''8971'_54 (coe v1)
            (coe v3))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v2))
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v1)
                        (coe v2))))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v2)))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.loopM
d_loopM_436 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_loopM_436 v0 v1 v2 ~v3 = du_loopM_436 v0 v1 v2
du_loopM_436 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> MAlonzo.Code.Once.IR.T_IR_16
du_loopM_436 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_Iter_130
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v1))
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'43'__22
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v2))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v1))))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.sigOpIR
d_sigOpIR_444 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_sigOpIR_444 ~v0 v1 v2 v3 = du_sigOpIR_444 v1 v2 v3
du_sigOpIR_444 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_sigOpIR_444 v0 v1 v2
  = let v3
          = case coe v2 of
              MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v4
                -> coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                        (coe (0 :: Integer)) (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                     (coe
                        MAlonzo.Code.Once.IR.C_SigOp_140
                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v0)
                        (coe
                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                           (coe v1) (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                           (coe v4)))
                     (coe MAlonzo.Code.Once.IR.C_terminal_72)
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                         -> case coe v8 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v9
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> case coe v2 of
                                            MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v13 v14
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C_curry_84
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_SigOp_140
                                                         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                                            (coe v1)
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                            (coe v14)))
                                                      (coe MAlonzo.Code.Once.IR.C_snd_48))
                                            MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v11
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe (0 :: Integer))
                                                      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_SigOp_140
                                                      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                                         (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                         (coe v11)))
                                                   (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> case coe v2 of
                                            MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v13 v14
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C_curry_84
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_SigOp_140
                                                         (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                         (coe v6)
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_246
                                                            (coe v6) (coe v5) (coe v1)
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                            (coe v14)))
                                                      (coe MAlonzo.Code.Once.IR.C_snd_48))
                                            MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v11
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                      (coe (0 :: Integer))
                                                      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_SigOp_140
                                                      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                      (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                                         (coe v1)
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                         (coe v11)))
                                                   (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> case coe v2 of
                                     MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v12 v13
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_84
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__28
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_140
                                                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_246
                                                     (coe v6) (coe v5) (coe v1)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                     (coe v13)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_48))
                                     MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v10
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                            (coe
                                               MAlonzo.Code.Once.IR.C_SigOp_140
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                                  (coe v1)
                                                  (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                                  (coe v10)))
                                            (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_One_10
                         -> case coe v2 of
                              MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v12 v13
                                -> coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe (0 :: Integer)) (coe v4))
                                        (coe
                                           MAlonzo.Code.Once.IR.C_SigOp_140 (coe v4) (coe v6)
                                           (coe
                                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_246
                                              (coe v6) (coe v5) (coe v1) (coe v12) (coe v13)))
                                        (coe MAlonzo.Code.Once.IR.C_snd_48))
                              MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v10
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__28
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                        (coe (0 :: Integer))
                                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_SigOp_140
                                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                           (coe v1) (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                           (coe v10)))
                                     (coe MAlonzo.Code.Once.IR.C_terminal_72)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v2 of
                              MAlonzo.Code.Once.Type.Concrete.C_con'45'fun_18 v12 v13
                                -> coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe (0 :: Integer)) (coe v4))
                                        (coe
                                           MAlonzo.Code.Once.IR.C_SigOp_140 (coe v4) (coe v6)
                                           (coe
                                              MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_246
                                              (coe v6) (coe v5) (coe v1) (coe v12) (coe v13)))
                                        (coe MAlonzo.Code.Once.IR.C_snd_48))
                              MAlonzo.Code.Once.Type.Concrete.C_con'45'base_10 v10
                                -> coe
                                     MAlonzo.Code.Once.IR.C__'8728'__28
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                        (coe (0 :: Integer))
                                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_SigOp_140
                                        (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_212
                                           (coe v1) (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
                                           (coe v10)))
                                     (coe MAlonzo.Code.Once.IR.C_terminal_72)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.Surface.Elaborate.elaborate
d_elaborate_514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate_514 v0 v1 v2 v3 v4 ~v5 v6
  = du_elaborate_514 v0 v1 v2 v3 v4 v6
du_elaborate_514 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate_514 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v8
        -> coe du_projUsed_178 (coe v2) (coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v9 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  seq (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                              (coe
                                                 MAlonzo.Code.Once.Context.du__'8638'__64
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2
                                                    v16)
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v19
                                                    v3))))
                                        (coe
                                           du_elaborate_514 (coe v0)
                                           (coe addInt (coe (1 :: Integer)) (coe v1))
                                           (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v16)
                                           (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v19 v3)
                                           (coe v18) (coe v15))
                                        (coe MAlonzo.Code.Once.IR.C_fst_42)))
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                  (coe
                                                     MAlonzo.Code.Once.Context.du__'8638'__64
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                                                        v2 v16)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                                                        v9 v3))))
                                            (coe
                                               du_elaborate_514 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v1))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2
                                                  v16)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v9
                                                  v3)
                                               (coe v18) (coe v15))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_514 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v1))
                                            (coe
                                               MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v16)
                                            (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v9 v3)
                                            (coe v18) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                               (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                                  (coe
                                                     MAlonzo.Code.Once.Context.du__'8638'__64
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.C__'9656'__16
                                                        v2 v16)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Context.C__'8759'__40
                                                        v9 v3))))
                                            (coe
                                               du_elaborate_514 (coe v0)
                                               (coe addInt (coe (1 :: Integer)) (coe v1))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2
                                                  v16)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v9
                                                  v3)
                                               (coe v18) (coe v15))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  MAlonzo.Code.Once.Spec.Grade.C_One_10
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_514 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v1))
                                            (coe
                                               MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v16)
                                            (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v9 v3)
                                            (coe v18) (coe v15))
                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_514 (coe v0)
                                            (coe addInt (coe (1 :: Integer)) (coe v1))
                                            (coe
                                               MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v16)
                                            (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v9 v3)
                                            (coe v18) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v8 v9 v10 v12 v13 v14
        -> case coe v12 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4)))
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                             (coe v4))
                          (coe v13))
                       (coe MAlonzo.Code.Once.IR.C_terminal_72))
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10)))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                          (coe
                             du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v12)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                (coe v4))
                             (coe v13))
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                          (coe
                             du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
                             (coe v14))
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                      (coe v9)))
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45''42'One_194
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                   (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                      (coe v9)))))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10)))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                          (coe
                             du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v12)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                (coe v4))
                             (coe v13))
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                          (coe
                             du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9) (coe v10)
                             (coe v14))
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                      (coe v9)))
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                   (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                                      (coe v9)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_72 v8 v9 v10 v13 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> coe
                           MAlonzo.Code.Once.IR.C_curry_84
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                    (coe
                                       MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                             (coe v9))))))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'8667'__24
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                          (coe v10))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                          (coe v18)))
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                       (coe v10)))
                                 (coe MAlonzo.Code.Once.IR.C_apply_90)
                                 (coe
                                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                    (coe
                                       MAlonzo.Code.Once.IR.C__'8728'__28
                                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                             (coe
                                                MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                (coe v8))))
                                       (coe
                                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                (coe v20))
                                             (coe v18))
                                          (coe v14))
                                       (coe
                                          du_env'737'_202 (coe v0) (coe v2) (coe v8)
                                          (coe
                                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                             (coe v9))))
                                    (coe
                                       MAlonzo.Code.Once.IR.C__'8728'__28
                                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                          (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                             (coe
                                                MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                (coe v9))))
                                       (coe
                                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9)
                                          (coe v10) (coe v15))
                                       (coe du_env'691'ω_246 (coe v0) (coe v2) (coe v8) (coe v9)))))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_86 v8 v9 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                             (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                       (coe
                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8) (coe v14)
                          (coe v12))
                       (coe du_env'737'_202 (coe v0) (coe v2) (coe v8) (coe v9)))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                             (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                       (coe
                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9) (coe v15)
                          (coe v13))
                       (coe du_env'691'_224 (coe v0) (coe v2) (coe v8) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_98 v10 v11
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v10)))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe
                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v4) (coe v10))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_110 v9 v11
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v9))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4)))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe
                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v9) (coe v4))
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_122 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v12))
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe
                       du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v12)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_134 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13))
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe
                       du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v13)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_156 v8 v9 v10 v11 v12 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'43'__22
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                               (coe v10)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13)))
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                               (coe v10)))))
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v14))))
             (coe
                MAlonzo.Code.Once.IR.C_case_68
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                      (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64
                            (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v13)
                            (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v9))))
                   (coe
                      du_elaborate_514 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1))
                      (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v13)
                      (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v9) (coe v4)
                      (coe v17))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                            (coe
                               MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                               (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13)))
                      (coe du_bindEnv_270 (coe v11))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                  (coe
                                     MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                                        (coe v10)))))
                            (coe
                               du_restrictEnv_118 (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9) (coe v10))
                               (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Context.du_'8849''7512''45''8852''737'_232
                                  (coe v9) (coe v10)))
                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                         (coe MAlonzo.Code.Once.IR.C_snd_48))))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                      (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64
                            (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v14)
                            (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v10))))
                   (coe
                      du_elaborate_514 (coe v0)
                      (coe addInt (coe (1 :: Integer)) (coe v1))
                      (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v14)
                      (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v10) (coe v4)
                      (coe v18))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                            (coe
                               MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                               (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v10))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v14)))
                      (coe du_bindEnv_270 (coe v12))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                  (coe
                                     MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                                        (coe v10)))))
                            (coe
                               du_restrictEnv_118 (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9) (coe v10))
                               (coe v10)
                               (coe
                                  MAlonzo.Code.Once.Context.du_'8849''7512''45''8852''691'_248
                                  (coe v9) (coe v10)))
                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                         (coe MAlonzo.Code.Once.IR.C_snd_48)))))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                               (coe v10)))))
                   (coe
                      MAlonzo.Code.Once.IRTy.C__'43'__22
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v14))))
                (coe
                   du_distribute_298
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                         (coe
                            MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                               (coe v10)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v13))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v14)))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                   (coe
                      du_restrictEnv_118 (coe v0) (coe v2)
                      (coe
                         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                         (coe
                            MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9) (coe v10)))
                      (coe
                         MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9) (coe v10))
                      (coe
                         MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142 (coe v8)
                         (coe
                            MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                            (coe v10))))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                         (coe v0)
                         (coe
                            MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                            (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                      (coe
                         du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                         (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v13) (coe v14))
                         (coe v16))
                      (coe
                         du_restrictEnv_118 (coe v0) (coe v2)
                         (coe
                            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v8)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9) (coe v10)))
                         (coe v8)
                         (coe
                            MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v8)
                            (coe
                               MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v9)
                               (coe v10)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_162
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_172 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Void_18)
             (coe MAlonzo.Code.Once.IR.C_initial_76)
             (coe
                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_188 v8 v9 v10 v11 v13 v14
        -> case coe v10 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    du_elaborate_514 (coe v0)
                    (coe addInt (coe (1 :: Integer)) (coe v1))
                    (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v11)
                    (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v9) (coe v4)
                    (coe v14)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                          (coe
                             MAlonzo.Code.Once.Context.du__'8638'__64
                             (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v11)
                             (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v9))))
                    (coe
                       du_elaborate_514 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v11)
                       (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v9) (coe v4)
                       (coe v14))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11)))
                       (coe du_bindEnv_270 (coe v10))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                   (coe v8)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                   (coe v8))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                   (coe
                                      MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                             (coe
                                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8) (coe v11)
                                (coe v13))
                             (coe
                                du_restrictEnv_118 (coe v0) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                      (coe v8)))
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                         (coe v8)))
                                   (coe
                                      MAlonzo.Code.Once.Context.du_'8849''7512''45''42'One_194
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                         (coe v8))))))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                          (coe
                             MAlonzo.Code.Once.Context.du__'8638'__64
                             (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v11)
                             (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v9))))
                    (coe
                       du_elaborate_514 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v2 v11)
                       (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v9) (coe v4)
                       (coe v14))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                             (coe
                                MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v9))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11)))
                       (coe du_bindEnv_270 (coe v10))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe
                             du_restrictEnv_118 (coe v0) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                   (coe v8)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Context.du_'8849''7512''45''43''737'_126 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                   (coe v8))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe v0)
                                (coe
                                   MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                   (coe
                                      MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                             (coe
                                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8) (coe v11)
                                (coe v13))
                             (coe
                                du_restrictEnv_118 (coe v0) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                      (coe v8)))
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                         (coe v8)))
                                   (coe
                                      MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v10)
                                         (coe v8))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_194 v8
        -> coe du_intLit_8 (coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_float_202 v8
        -> coe du_floatLit_14 (coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_num_216 v9 v10 v11 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v9) (coe v11)))
             (coe du_numIR_60 (coe v9) (coe v11) (coe v12) (coe v13))
             (coe
                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v9) (coe v11))
                (coe v14))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_228 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.CoerceIR.du_runCoe_410 (coe v0) (coe v9)
             (coe v4) (coe v11)
             (coe
                du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_236 v8 v9 v10
        -> coe du_sigOpIR_444 (coe v8) (coe v9) (coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_244 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (MAlonzo.Code.Once.IR.Ref.d_refIR_10
                (coe v0) (coe v4)
                (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v9)))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_254 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (MAlonzo.Code.Once.IR.Ref.d_refIR_10
                (coe v0) (coe v4)
                (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v8)))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_262 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                (coe v0)
                (coe
                   MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                   (coe
                      MAlonzo.Code.Once.Context.du__'8638'__64
                      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
                      (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36))))
             (coe
                du_elaborate_514 (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
                (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36) (coe v4)
                (coe v9))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_274 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_84
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v12)) v11
                       (coe MAlonzo.Code.Once.IR.C_snd_48))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_286 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v9)) v11
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                   (coe v0)
                   (coe
                      MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                      (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                (coe
                   du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8) (coe v9)
                   (coe v12))
                (coe
                   du_restrictEnv_118 (coe v0) (coe v2)
                   (coe
                      MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                      (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v1))
                      (coe
                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Context.du_'8849''7512''45'trans_180 (coe v8)
                      (coe
                         MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                      (coe
                         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                         (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v1))
                         (coe
                            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8)))
                      (coe
                         MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206 (coe v8))
                      (coe
                         MAlonzo.Code.Once.Context.du_'8849''7512''45''43''691'_142
                         (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_44 (coe v1))
                         (coe
                            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                            (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))))))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_304 v8 v9 v11 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v18)))
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v16))
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11))))
                           (coe
                              du_compIR_348
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v16))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v11))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v18)))
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                          (coe v8))))
                                 (coe
                                    du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                       (coe v18))
                                    (coe v14))
                                 (coe
                                    du_env'737'_202 (coe v0) (coe v2) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v9))))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                    (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                       (coe
                                          MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                          (coe v9))))
                                 (coe
                                    du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v16)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v20))
                                       (coe v11))
                                    (coe v15))
                                 (coe du_env'691'ω_246 (coe v0) (coe v2) (coe v8) (coe v9))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_322 v8 v9 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v19 v20
                      -> case coe v17 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v18)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v20))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v18))))
                                  (coe
                                     du_copairIR_360
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v19))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v18)))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                              (coe
                                                 MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                 (coe v8))))
                                        (coe
                                           du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v19)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v22))
                                              (coe v18))
                                           (coe v14))
                                        (coe du_env'737'_202 (coe v0) (coe v2) (coe v8) (coe v9)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                              (coe
                                                 MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                 (coe v9))))
                                        (coe
                                           du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v20)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v22))
                                              (coe v18))
                                           (coe v15))
                                        (coe du_env'691'_224 (coe v0) (coe v2) (coe v8) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_340 v8 v9 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v16))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v21)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v16))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v22))))
                                  (coe
                                     du_forkIR_372
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v16))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v21))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v22)))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                              (coe
                                                 MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                 (coe v8))))
                                        (coe
                                           du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v20))
                                              (coe v21))
                                           (coe v14))
                                        (coe du_env'737'_202 (coe v0) (coe v2) (coe v8) (coe v9)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                           (coe v0)
                                           (coe
                                              MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                              (coe
                                                 MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                                 (coe v9))))
                                        (coe
                                           du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v20))
                                              (coe v22))
                                           (coe v15))
                                        (coe du_env'691'_224 (coe v0) (coe v2) (coe v8) (coe v9))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_358 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'42'__20
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                           (coe v18)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v20)))
                                  (coe
                                     du_curryIR_384
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v15))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v18))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v20)))
                                  (coe
                                     du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v15)
                                           (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                        (coe v20))
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_374 v8 v10 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v18) (coe v17)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                        (coe v17)))
                                  (coe du_cataM_396 (coe v0) (coe v18) (coe v17) (coe v13))
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__28
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                        (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                           (coe
                                              MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2)
                                              (coe v8))))
                                     (coe
                                        du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                              (coe v18) (coe v17))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v20))
                                           (coe v17))
                                        (coe v14))
                                     (coe
                                        du_restrictEnv_118 (coe v0) (coe v2)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                                        (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                           (coe v8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_392 v8 v10 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C_ν_30 v19 v20
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'8667'__24
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v16))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v19)
                                    (coe v16))))
                           (coe du_anaM_418 (coe v0) (coe v19) (coe v16) (coe v14))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                    (coe
                                       MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                              (coe
                                 du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v16)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v20)))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v19)
                                       (coe v16)))
                                 (coe v15))
                              (coe
                                 du_restrictEnv_118 (coe v0) (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                                    (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_404 v8 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'8667'__24
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v12))
                       (coe
                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                          (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v12))))
                    (coe du_loopM_436 (coe v0) (coe v12) (coe v14))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                             (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v8))))
                       (coe
                          du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v8)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                             (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v14) (coe v12)))
                          (coe v11))
                       (coe
                          du_restrictEnv_118 (coe v0) (coe v2)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v8))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Context.du_'8849''7512''45''42'Many_206
                             (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.eraseCtx
d_eraseCtx_862 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eraseCtx_862 v0 ~v1 v2 ~v3 v4 = du_eraseCtx_862 v0 v2 v4
du_eraseCtx_862 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eraseCtx_862 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v2) (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v4)))
                           (coe du_eraseCtx_862 (coe v0) (coe v4) (coe v8))
                           (coe MAlonzo.Code.Once.IR.C_fst_42)
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v4)))
                              (coe du_eraseCtx_862 (coe v0) (coe v4) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe MAlonzo.Code.Once.IR.C_snd_48)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v4)))
                              (coe du_eraseCtx_862 (coe v0) (coe v4) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe MAlonzo.Code.Once.IR.C_snd_48)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborateFull
d_elaborateFull_900 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborateFull_900 v0 v1 v2 v3 v4 ~v5 v6
  = du_elaborateFull_900 v0 v1 v2 v3 v4 v6
du_elaborateFull_900 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborateFull_900 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
         (coe v0)
         (coe
            MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
            (coe MAlonzo.Code.Once.Context.du__'8638'__64 (coe v2) (coe v3))))
      (coe
         du_elaborate_514 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe du_eraseCtx_862 (coe v0) (coe v2) (coe v3))
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_920 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate'45'default_920 v0 v1 v2 v3 v4
  = coe
      du_elaborateFull_900 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.Surface.Elaborate.distribute-default
d_distribute'45'default_928 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute'45'default_928 v0 v1 v2
  = coe du_distribute_298 (coe v0) (coe v1) (coe v2)
