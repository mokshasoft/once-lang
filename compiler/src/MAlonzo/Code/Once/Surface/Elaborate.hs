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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.CoerceIR
import qualified MAlonzo.Code.Once.Surface.Syntax

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
         MAlonzo.Code.Once.IR.C_const_126
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'int_512) v0)
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
         MAlonzo.Code.Once.IR.C_const_126
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'float_514) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_72)
-- Once.Surface.Elaborate.addIR
d_addIR_18 :: MAlonzo.Code.Once.IR.T_IR_16
d_addIR_18
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
-- Once.Surface.Elaborate.subIR
d_subIR_20 :: MAlonzo.Code.Once.IR.T_IR_16
d_subIR_20
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
-- Once.Surface.Elaborate.mulIR
d_mulIR_22 :: MAlonzo.Code.Once.IR.T_IR_16
d_mulIR_22
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
-- Once.Surface.Elaborate.divIR
d_divIR_24 :: MAlonzo.Code.Once.IR.T_IR_16
d_divIR_24
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
-- Once.Surface.Elaborate.modIR
d_modIR_26 :: MAlonzo.Code.Once.IR.T_IR_16
d_modIR_26
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
-- Once.Surface.Elaborate.faddIR
d_faddIR_28 :: MAlonzo.Code.Once.IR.T_IR_16
d_faddIR_28
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
-- Once.Surface.Elaborate.fsubIR
d_fsubIR_30 :: MAlonzo.Code.Once.IR.T_IR_16
d_fsubIR_30
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
-- Once.Surface.Elaborate.fmulIR
d_fmulIR_32 :: MAlonzo.Code.Once.IR.T_IR_16
d_fmulIR_32
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
-- Once.Surface.Elaborate.fdivIR
d_fdivIR_34 :: MAlonzo.Code.Once.IR.T_IR_16
d_fdivIR_34
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
         (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
-- Once.Surface.Elaborate.i2fIR
d_i2fIR_36 :: MAlonzo.Code.Once.IR.T_IR_16
d_i2fIR_36
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136)
-- Once.Surface.Elaborate.negIR
d_negIR_38 :: MAlonzo.Code.Once.IR.T_IR_16
d_negIR_38
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124)
-- Once.Surface.Elaborate.ltIR
d_ltIR_40 :: MAlonzo.Code.Once.IR.T_IR_16
d_ltIR_40
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
-- Once.Surface.Elaborate.leIR
d_leIR_42 :: MAlonzo.Code.Once.IR.T_IR_16
d_leIR_42
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
-- Once.Surface.Elaborate.gtIR
d_gtIR_44 :: MAlonzo.Code.Once.IR.T_IR_16
d_gtIR_44
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
-- Once.Surface.Elaborate.geIR
d_geIR_46 :: MAlonzo.Code.Once.IR.T_IR_16
d_geIR_46
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
-- Once.Surface.Elaborate.eqIR
d_eqIR_48 :: MAlonzo.Code.Once.IR.T_IR_16
d_eqIR_48
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
-- Once.Surface.Elaborate.neIR
d_neIR_50 :: MAlonzo.Code.Once.IR.T_IR_16
d_neIR_50
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_132
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'42'__24
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
         (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'43'__26
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
-- Once.Surface.Elaborate.proj
d_proj_58 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_proj_58 ~v0 v1 v2 = du_proj_58 v1 v2
du_proj_58 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_proj_58 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_48
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                          (coe v3)))
                    (coe du_proj_58 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_42)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.restrictEnv
d_restrictEnv_84 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_restrictEnv_84 ~v0 v1 v2 v3 ~v4 v5
  = du_restrictEnv_84 v1 v2 v3 v5
du_restrictEnv_84 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_restrictEnv_84 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8
        -> coe seq (coe v3) (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v5 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Context.C__'8849''8759'__192 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v16 v17
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v19 v20
                             -> case coe v13 of
                                  MAlonzo.Code.Once.Lang.Context.C_z'8804'z_164
                                    -> coe du_restrictEnv_84 (coe v5) (coe v17) (coe v20) (coe v14)
                                  MAlonzo.Code.Once.Lang.Context.C_z'8804'o_166
                                    -> coe
                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                  (coe v5) (coe v17))))
                                         (coe
                                            du_restrictEnv_84 (coe v5) (coe v17) (coe v20)
                                            (coe v14))
                                         (coe MAlonzo.Code.Once.IR.C_fst_42)
                                  MAlonzo.Code.Once.Lang.Context.C_z'8804'm_168
                                    -> coe
                                         MAlonzo.Code.Once.IR.C__'8728'__28
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                  (coe v5) (coe v17))))
                                         (coe
                                            du_restrictEnv_84 (coe v5) (coe v17) (coe v20)
                                            (coe v14))
                                         (coe MAlonzo.Code.Once.IR.C_fst_42)
                                  MAlonzo.Code.Once.Lang.Context.C_o'8804'o_170
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_84 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                         (coe MAlonzo.Code.Once.IR.C_snd_48)
                                  MAlonzo.Code.Once.Lang.Context.C_o'8804'm_172
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_84 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                         (coe MAlonzo.Code.Once.IR.C_snd_48)
                                  MAlonzo.Code.Once.Lang.Context.C_m'8804'm_174
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_84 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                         (coe MAlonzo.Code.Once.IR.C_snd_48)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.projUsed
d_projUsed_154 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_projUsed_154 ~v0 v1 v2 = du_projUsed_154 v1 v2
du_projUsed_154 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_projUsed_154 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_48
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_projUsed_154 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.envˡ
d_env'737'_180 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'737'_180 ~v0 v1 ~v2 v3 v4 = du_env'737'_180 v1 v3 v4
du_env'737'_180 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'737'_180 v0 v1 v2
  = coe
      du_restrictEnv_84 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
         (coe v1) (coe v2))
-- Once.Surface.Elaborate.envʳ
d_env'691'_200 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'691'_200 ~v0 v1 ~v2 v3 v4 = du_env'691'_200 v1 v3 v4
du_env'691'_200 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'691'_200 v0 v1 v2
  = coe
      du_restrictEnv_84 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe v2))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v1) (coe v2))
-- Once.Surface.Elaborate.envʳω
d_env'691'ω_220 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'691'ω_220 ~v0 v1 ~v2 v3 v4 = du_env'691'ω_220 v1 v3 v4
du_env'691'ω_220 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'691'ω_220 v0 v1 v2
  = coe
      du_restrictEnv_84 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
         (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2)))
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
            (coe v2))
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
            (coe v1)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v2))))
-- Once.Surface.Elaborate.bindEnv
d_bindEnv_242 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_bindEnv_242 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_bindEnv_242 v5
du_bindEnv_242 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_bindEnv_242 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe MAlonzo.Code.Once.IR.C_fst_42
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe MAlonzo.Code.Once.IR.C_id_20
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe MAlonzo.Code.Once.IR.C_id_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_260 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swap''_260 ~v0 ~v1 ~v2 = du_swap''_260
du_swap''_260 :: MAlonzo.Code.Once.IR.T_IR_16
du_swap''_260
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
      (coe MAlonzo.Code.Once.IR.C_snd_48)
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Surface.Elaborate.distribute
d_distribute_270 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute_270 v0 v1 v2 ~v3 = du_distribute_270 v0 v1 v2
du_distribute_270 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribute_270 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
         (coe v0))
      (coe du_distrib''_290 (coe v0) (coe v1) (coe v2))
      (coe du_swap''_260)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_284 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInlSwap_284 v0 v1 ~v2 ~v3 = du_curryInlSwap_284 v0 v1
du_curryInlSwap_284 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInlSwap_284 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swap''_260))
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_286 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInrSwap_286 v0 ~v1 v2 ~v3 = du_curryInrSwap_286 v0 v2
du_curryInrSwap_286 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInrSwap_286 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__28
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_60) (coe du_swap''_260))
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_288 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryDistrib_288 v0 v1 v2 ~v3 = du_curryDistrib_288 v0 v1 v2
du_curryDistrib_288 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryDistrib_288 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_case_68
      (coe du_curryInlSwap_284 (coe v0) (coe v1))
      (coe du_curryInrSwap_286 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_290 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distrib''_290 v0 v1 v2 ~v3 = du_distrib''_290 v0 v1 v2
du_distrib''_290 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distrib''_290 v0 v1 v2
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
            (coe du_curryDistrib_288 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_42))
         (coe MAlonzo.Code.Once.IR.C_snd_48))
-- Once.Surface.Elaborate.swapIR
d_swapIR_296 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swapIR_296 ~v0 ~v1 ~v2 = du_swapIR_296
du_swapIR_296 :: MAlonzo.Code.Once.IR.T_IR_16
du_swapIR_296
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
      (coe MAlonzo.Code.Once.IR.C_snd_48)
      (coe MAlonzo.Code.Once.IR.C_fst_42)
-- Once.Surface.Elaborate.distribIR
d_distribIR_308 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribIR_308 v0 v1 v2 ~v3 = du_distribIR_308 v0 v1 v2
du_distribIR_308 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribIR_308 v0 v1 v2
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
                     (coe MAlonzo.Code.Once.IR.C_inl_54) (coe du_swapIR_296)))
               (coe
                  MAlonzo.Code.Once.IR.C_curry_84
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__28
                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))
                     (coe MAlonzo.Code.Once.IR.C_inr_60) (coe du_swapIR_296))))
            (coe MAlonzo.Code.Once.IR.C_snd_48))
         (coe MAlonzo.Code.Once.IR.C_fst_42))
-- Once.Surface.Elaborate.compIR
d_compIR_320 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_compIR_320 v0 v1 v2 ~v3 = du_compIR_320 v0 v1 v2
du_compIR_320 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_compIR_320 v0 v1 v2
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
d_copairIR_332 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_copairIR_332 v0 v1 v2 ~v3 = du_copairIR_332 v0 v1 v2
du_copairIR_332 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_copairIR_332 v0 v1 v2
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
            du_distribIR_308
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
            (coe v0) (coe v1)))
-- Once.Surface.Elaborate.forkIR
d_forkIR_344 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_forkIR_344 v0 v1 v2 ~v3 = du_forkIR_344 v0 v1 v2
du_forkIR_344 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_forkIR_344 v0 v1 v2
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
d_curryIR_356 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryIR_356 v0 v1 v2 ~v3 = du_curryIR_356 v0 v1 v2
du_curryIR_356 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryIR_356 v0 v1 v2
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
d_cataM_364 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_cataM_364 v0 v1 v2 ~v3 = du_cataM_364 v0 v1 v2
du_cataM_364 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_cataM_364 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_Cata_106
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                     (coe
                        MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                        (coe v1)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                     (coe v1))))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.anaM
d_anaM_382 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_anaM_382 v0 v1 ~v2 v3 ~v4 = du_anaM_382 v0 v1 v3
du_anaM_382 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_anaM_382 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_84
      (coe
         MAlonzo.Code.Once.IR.C_Ana_122
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__28
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1))
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                     (coe
                        MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v0)
                        (coe v1))))
               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v1)))
            (coe MAlonzo.Code.Once.IR.C_apply_90)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
               (coe MAlonzo.Code.Once.IR.C_fst_42)
               (coe MAlonzo.Code.Once.IR.C_snd_48))))
-- Once.Surface.Elaborate.elaborate
d_elaborate_402 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate_402 v0 v1 v2 v3 ~v4 v5
  = du_elaborate_402 v0 v1 v2 v3 v5
du_elaborate_402 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate_402 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v7
        -> coe du_projUsed_154 (coe v1) (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v8 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.IR.C_curry_84
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                    (coe v1) (coe v15))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v18
                                                    v2))))
                                        (coe
                                           du_elaborate_402
                                           (coe addInt (coe (1 :: Integer)) (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1)
                                              (coe v15))
                                           (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v18 v2)
                                           (coe v17) (coe v14))
                                        (coe MAlonzo.Code.Once.IR.C_fst_42)))
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> case coe v8 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                        (coe v1) (coe v15))
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                                                        v8 v2))))
                                            (coe
                                               du_elaborate_402
                                               (coe addInt (coe (1 :: Integer)) (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                  (coe v1) (coe v15))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v8
                                                  v2)
                                               (coe v17) (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_402
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1)
                                               (coe v15))
                                            (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v8 v2)
                                            (coe v17) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v8 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                        (coe v1) (coe v15))
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                                                        v8 v2))))
                                            (coe
                                               du_elaborate_402
                                               (coe addInt (coe (1 :: Integer)) (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                  (coe v1) (coe v15))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v8
                                                  v2)
                                               (coe v17) (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_402
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1)
                                               (coe v15))
                                            (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v8 v2)
                                            (coe v17) (coe v14))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_84
                                         (coe
                                            du_elaborate_402
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1)
                                               (coe v15))
                                            (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v8 v2)
                                            (coe v17) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v7 v8 v9 v11 v12 v13
        -> case coe v11 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          du_elaborate_402 (coe v0) (coe v1) (coe v7)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v11)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v3))
                          (coe v12))
                       (coe MAlonzo.Code.Once.IR.C_terminal_72))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9)))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v7))))
                          (coe
                             du_elaborate_402 (coe v0) (coe v1) (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v11)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                (coe v3))
                             (coe v12))
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))
                             (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v8))))
                          (coe
                             du_elaborate_402 (coe v0) (coe v1) (coe v8) (coe v9) (coe v13))
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                      (coe v8)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                      (coe v8)))))))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9)))
                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v7))))
                          (coe
                             du_elaborate_402 (coe v0) (coe v1) (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v11)
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                (coe v3))
                             (coe v12))
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))
                             (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__28
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v8))))
                          (coe
                             du_elaborate_402 (coe v0) (coe v1) (coe v8) (coe v9) (coe v13))
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                      (coe v8)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                      (coe v8)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v7 v8 v9 v12 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v18 v19
                      -> coe
                           MAlonzo.Code.Once.IR.C_curry_84
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v8))))))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (coe
                                    MAlonzo.Code.Once.IRTy.C__'42'__20
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'8667'__24
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9))
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                                    (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9)))
                                 (coe MAlonzo.Code.Once.IR.C_apply_90)
                                 (coe
                                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                    (coe
                                       MAlonzo.Code.Once.IR.C__'8728'__28
                                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                             (coe
                                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                (coe v1) (coe v7))))
                                       (coe
                                          du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                (coe v19))
                                             (coe v17))
                                          (coe v13))
                                       (coe
                                          du_env'737'_180 (coe v1) (coe v7)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                             (coe v8))))
                                    (coe
                                       MAlonzo.Code.Once.IR.C__'8728'__28
                                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                          (coe
                                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                             (coe
                                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                (coe v1) (coe v8))))
                                       (coe
                                          du_elaborate_402 (coe v0) (coe v1) (coe v8) (coe v9)
                                          (coe v14))
                                       (coe du_env'691'ω_220 (coe v1) (coe v7) (coe v8)))))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v7 v8 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                       (coe
                          du_elaborate_402 (coe v0) (coe v1) (coe v7) (coe v13) (coe v11))
                       (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                       (coe
                          du_elaborate_402 (coe v0) (coe v1) (coe v8) (coe v14) (coe v12))
                       (coe du_env'691'_200 (coe v1) (coe v7) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v9)))
             (coe MAlonzo.Code.Once.IR.C_fst_42)
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v9))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v8 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v8))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
             (coe MAlonzo.Code.Once.IR.C_snd_48)
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v8) (coe v3))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v11))
                    (coe MAlonzo.Code.Once.IR.C_inl_54)
                    (coe
                       du_elaborate_402 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v12))
                    (coe MAlonzo.Code.Once.IR.C_inr_60)
                    (coe
                       du_elaborate_402 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'43'__22
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v12)))
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v13))))
             (coe
                MAlonzo.Code.Once.IR.C_case_68
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v10 v8))))
                   (coe
                      du_elaborate_402 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v12))
                      (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v10 v8) (coe v3)
                      (coe v16))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                  (coe v8))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v12)))
                      (coe du_bindEnv_242 (coe v10))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                        (coe v8) (coe v9)))))
                            (coe
                               du_restrictEnv_84 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                                  (coe v9))
                               (coe v8)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
                                  (coe v8) (coe v9)))
                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                         (coe MAlonzo.Code.Once.IR.C_snd_48))))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v13))
                            (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v9))))
                   (coe
                      du_elaborate_402 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v13))
                      (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v9) (coe v3)
                      (coe v17))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                  (coe v9))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v13)))
                      (coe du_bindEnv_242 (coe v11))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                                        (coe v8) (coe v9)))))
                            (coe
                               du_restrictEnv_84 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                                  (coe v9))
                               (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
                                  (coe v8) (coe v9)))
                            (coe MAlonzo.Code.Once.IR.C_fst_42))
                         (coe MAlonzo.Code.Once.IR.C_snd_48)))))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))))
                   (coe
                      MAlonzo.Code.Once.IRTy.C__'43'__22
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v12))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v13))))
                (coe
                   du_distribute_270
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v12))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v13)))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                   (coe
                      du_restrictEnv_84 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                            (coe v9)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                         (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                            (coe v9))))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__28
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                      (coe
                         du_elaborate_402 (coe v0) (coe v1) (coe v7)
                         (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v12) (coe v13))
                         (coe v15))
                      (coe
                         du_restrictEnv_84 (coe v1)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))
                         (coe v7)
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                            (coe v7)
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v8)
                               (coe v9)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe MAlonzo.Code.Once.IR.C_terminal_72
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Void_18)
             (coe MAlonzo.Code.Once.IR.C_initial_76)
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v7 v8 v9 v10 v12 v13
        -> case coe v9 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    du_elaborate_402 (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v10))
                    (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v8) (coe v3)
                    (coe v13)
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v10))
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v8))))
                    (coe
                       du_elaborate_402 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v10))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v8) (coe v3)
                       (coe v13))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v8))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10)))
                       (coe du_bindEnv_242 (coe v9))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v7)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v7))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                      (coe v7))))
                             (coe
                                du_elaborate_402 (coe v0) (coe v1) (coe v7) (coe v10) (coe v12))
                             (coe
                                du_restrictEnv_84 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                      (coe v7)))
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                         (coe v7)))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                         (coe v7))))))))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v10))
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v8))))
                    (coe
                       du_elaborate_402 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v10))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v9 v8) (coe v3)
                       (coe v13))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                   (coe v8))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10)))
                       (coe du_bindEnv_242 (coe v9))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                          (coe
                             du_restrictEnv_84 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v7)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                   (coe v7))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__28
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                      (coe v7))))
                             (coe
                                du_elaborate_402 (coe v0) (coe v1) (coe v7) (coe v10) (coe v12))
                             (coe
                                du_restrictEnv_84 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                      (coe v7)))
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                         (coe v7)))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v9)
                                         (coe v7))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v7
        -> coe du_intLit_8 (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v7
        -> coe du_floatLit_14 (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_addIR_18
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_subIR_20
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_mulIR_22
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_faddIR_28
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fsubIR_30
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fmulIR_32
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fdivIR_34
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Int_30) d_i2fIR_36
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_divIR_24
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_modIR_26
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Int_30) d_negIR_38
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_ltIR_40
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_leIR_42
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_gtIR_44
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_geIR_46
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_eqIR_48
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_neIR_50
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9))
                   (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__28
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v8))))
                   (coe
                      du_elaborate_402 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10))
                   (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Surface.CoerceIR.du_runCoe_386 (coe v8) (coe v3)
             (coe v10)
             (coe
                du_elaborate_402 (coe v0) (coe v1) (coe v2) (coe v8) (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v8 v9
        -> let v10
                 = case coe v9 of
                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v11
                       -> coe
                            MAlonzo.Code.Once.IR.C__'8728'__28
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                            (coe
                               MAlonzo.Code.Once.IR.C_SigOp_132
                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v3)
                               (coe
                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                  (coe v8)
                                  (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                  (coe v11)))
                            (coe MAlonzo.Code.Once.IR.C_terminal_72)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v11 v12 v13
                  -> case coe v12 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v14 v15
                         -> case coe v14 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                       -> case coe v9 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v19 v20
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C_curry_84
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_SigOp_132
                                                         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                         (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                            (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                            (coe v20)))
                                                      (coe MAlonzo.Code.Once.IR.C_snd_48))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_SigOp_132
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                         (coe v17)))
                                                   (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                       -> case coe v9 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v19 v20
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C_curry_84
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_SigOp_132
                                                         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                         (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                            (coe v13) (coe v12) (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                            (coe v20)))
                                                      (coe MAlonzo.Code.Once.IR.C_snd_48))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_SigOp_132
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                         (coe v17)))
                                                   (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                       -> case coe v9 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v19 v20
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C_curry_84
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C_SigOp_132
                                                         (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                         (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                            (coe v13) (coe v12) (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                            (coe v20)))
                                                      (coe MAlonzo.Code.Once.IR.C_snd_48))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                                              -> coe
                                                   MAlonzo.Code.Once.IR.C__'8728'__28
                                                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                                   (coe
                                                      MAlonzo.Code.Once.IR.C_SigOp_132
                                                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                         (coe v17)))
                                                   (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v19 v20
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_84
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__28
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_132 (coe v11)
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                     (coe v13) (coe v12) (coe v8) (coe v19)
                                                     (coe v20)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_48))
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                            (coe
                                               MAlonzo.Code.Once.IR.C_SigOp_132
                                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v3)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                  (coe v17)))
                                            (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v19 v20
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_84
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__28
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_132 (coe v11)
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                     (coe v13) (coe v12) (coe v8) (coe v19)
                                                     (coe v20)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_48))
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v17
                                       -> coe
                                            MAlonzo.Code.Once.IR.C__'8728'__28
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                                            (coe
                                               MAlonzo.Code.Once.IR.C_SigOp_132
                                               (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v3)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                  (coe v17)))
                                            (coe MAlonzo.Code.Once.IR.C_terminal_72)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (MAlonzo.Code.Once.IR.Ref.d_refIR_8
                (coe v3) (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v8)))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (MAlonzo.Code.Once.IR.Ref.d_refIR_8
                (coe v3) (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v7)))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                (coe
                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                      (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48))))
             (coe
                du_elaborate_402 (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v3)
                (coe v8))
             (coe MAlonzo.Code.Once.IR.C_terminal_72)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_84
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__28
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v11)) v10
                       (coe MAlonzo.Code.Once.IR.C_snd_48))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v8)) v10
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__28
                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v7))))
                (coe
                   du_elaborate_402 (coe v0) (coe v1) (coe v7) (coe v8) (coe v11))
                (coe
                   du_restrictEnv_84 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7)))
                   (coe v7)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                      (coe v7)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                         (coe v7))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))))))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v7 v8 v10 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v18 v19
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))))
                           (coe
                              du_compIR_320
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                          (coe v7))))
                                 (coe
                                    du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v19))
                                       (coe v17))
                                    (coe v13))
                                 (coe
                                    du_env'737'_180 (coe v1) (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                          (coe v8))))
                                 (coe
                                    du_elaborate_402 (coe v0) (coe v1) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v19))
                                       (coe v10))
                                    (coe v14))
                                 (coe du_env'691'ω_220 (coe v1) (coe v7) (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v7 v8 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v18 v19
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v18))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v19))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17))))
                                  (coe
                                     du_copairIR_332
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v18))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v19))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                 (coe v1) (coe v7))))
                                        (coe
                                           du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v18)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe v21))
                                              (coe v17))
                                           (coe v13))
                                        (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                 (coe v1) (coe v8))))
                                        (coe
                                           du_elaborate_402 (coe v0) (coe v1) (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v19)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe v21))
                                              (coe v17))
                                           (coe v14))
                                        (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v7 v8 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v18 v19
                      -> case coe v17 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v20)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v21))))
                                  (coe
                                     du_forkIR_344
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v20))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v21)))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                 (coe v1) (coe v7))))
                                        (coe
                                           du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v15)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe v19))
                                              (coe v20))
                                           (coe v13))
                                        (coe du_env'737'_180 (coe v1) (coe v7) (coe v8)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__28
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                                 (coe v1) (coe v8))))
                                        (coe
                                           du_elaborate_402 (coe v0) (coe v1) (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                              (coe v15)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe v19))
                                              (coe v21))
                                           (coe v14))
                                        (coe du_env'691'_200 (coe v1) (coe v7) (coe v8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'42'__20
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17)))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v19)))
                                  (coe
                                     du_curryIR_356
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v17))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v19)))
                                  (coe
                                     du_elaborate_402 (coe v0) (coe v1) (coe v2)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v14)
                                           (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v21))
                                        (coe v19))
                                     (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v7 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v13 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__28
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v16) (coe v15)))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v15)))
                                  (coe du_cataM_364 (coe v16) (coe v15) (coe v11))
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__28
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                           (coe
                                              MAlonzo.Code.Once.Lang.Context.du__'8638'__136
                                              (coe v1) (coe v7))))
                                     (coe
                                        du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                              (coe v16) (coe v15))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v18))
                                           (coe v15))
                                        (coe v12))
                                     (coe
                                        du_restrictEnv_84 (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v7))
                                        (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                           (coe v7))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v7 v12 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v17 v18
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'8667'__24
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v14))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v17)
                                    (coe v14))))
                           (coe du_anaM_382 (coe v17) (coe v14) (coe v12))
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1)
                                       (coe v7))))
                              (coe
                                 du_elaborate_402 (coe v0) (coe v1) (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v14)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v18))
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v17)
                                       (coe v14)))
                                 (coe v13))
                              (coe
                                 du_restrictEnv_84 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                                 (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                    (coe v7))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.eraseCtx
d_eraseCtx_988 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eraseCtx_988 ~v0 v1 ~v2 v3 = du_eraseCtx_988 v1 v3
du_eraseCtx_988 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eraseCtx_988 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8
        -> coe seq (coe v1) (coe MAlonzo.Code.Once.IR.C_id_20)
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                 (coe v3)))
                           (coe du_eraseCtx_988 (coe v3) (coe v8))
                           (coe MAlonzo.Code.Once.IR.C_fst_42)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                    (coe v3)))
                              (coe du_eraseCtx_988 (coe v3) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe MAlonzo.Code.Once.IR.C_snd_48)
                    MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__28
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                    (coe v3)))
                              (coe du_eraseCtx_988 (coe v3) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_42))
                           (coe MAlonzo.Code.Once.IR.C_snd_48)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborateFull
d_elaborateFull_1030 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborateFull_1030 v0 v1 v2 v3 ~v4 v5
  = du_elaborateFull_1030 v0 v1 v2 v3 v5
du_elaborateFull_1030 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborateFull_1030 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__28
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8638'__136 (coe v1) (coe v2))))
      (coe du_elaborate_402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe du_eraseCtx_988 (coe v1) (coe v2))
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_1048 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate'45'default_1048 v0 v1 v2 v3
  = coe du_elaborateFull_1030 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Surface.Elaborate.distribute-default
d_distribute'45'default_1056 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute'45'default_1056 v0 v1 v2
  = coe du_distribute_270 (coe v0) (coe v1) (coe v2)
