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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Surface.Elaborate.intLit
d_intLit_8 ::
  Integer ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_intLit_8 v0 ~v1 = du_intLit_8 v0
du_intLit_8 :: Integer -> MAlonzo.Code.Once.IR.T_IR_16
du_intLit_8 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_150
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'int_528) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.strLit
d_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_strLit_14 v0 ~v1 = du_strLit_14 v0
du_strLit_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_strLit_14 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe
         MAlonzo.Code.Once.IR.C_SigOp_156
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Str_136)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_408
            (coe v0)))
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.floatLit
d_floatLit_20 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_floatLit_20 v0 ~v1 = du_floatLit_20 v0
du_floatLit_20 ::
  MAlonzo.Code.Once.Float.Decimal.T_Decimal_6 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_floatLit_20 v0
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe
         MAlonzo.Code.Once.IR.C_const_150
         (coe MAlonzo.Code.Once.IRTy.C_fits'45'float_530) v0)
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.Surface.Elaborate.addIR
d_addIR_24 :: MAlonzo.Code.Once.IR.T_IR_16
d_addIR_24
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_370)
-- Once.Surface.Elaborate.subIR
d_subIR_26 :: MAlonzo.Code.Once.IR.T_IR_16
d_subIR_26
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_372)
-- Once.Surface.Elaborate.mulIR
d_mulIR_28 :: MAlonzo.Code.Once.IR.T_IR_16
d_mulIR_28
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_374)
-- Once.Surface.Elaborate.divIR
d_divIR_30 :: MAlonzo.Code.Once.IR.T_IR_16
d_divIR_30
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_376)
-- Once.Surface.Elaborate.modIR
d_modIR_32 :: MAlonzo.Code.Once.IR.T_IR_16
d_modIR_32
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_378)
-- Once.Surface.Elaborate.faddIR
d_faddIR_34 :: MAlonzo.Code.Once.IR.T_IR_16
d_faddIR_34
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe MAlonzo.Code.Once.Type.C_Float_134))
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_386)
-- Once.Surface.Elaborate.fsubIR
d_fsubIR_36 :: MAlonzo.Code.Once.IR.T_IR_16
d_fsubIR_36
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe MAlonzo.Code.Once.Type.C_Float_134))
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_388)
-- Once.Surface.Elaborate.fmulIR
d_fmulIR_38 :: MAlonzo.Code.Once.IR.T_IR_16
d_fmulIR_38
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe MAlonzo.Code.Once.Type.C_Float_134))
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_390)
-- Once.Surface.Elaborate.fdivIR
d_fdivIR_40 :: MAlonzo.Code.Once.IR.T_IR_16
d_fdivIR_40
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe MAlonzo.Code.Once.Type.C_Float_134))
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_392)
-- Once.Surface.Elaborate.i2fIR
d_i2fIR_42 :: MAlonzo.Code.Once.IR.T_IR_16
d_i2fIR_42
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Type.C_Float_134)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_394)
-- Once.Surface.Elaborate.negIR
d_negIR_44 :: MAlonzo.Code.Once.IR.T_IR_16
d_negIR_44
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Type.C_Int_132)
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_380)
-- Once.Surface.Elaborate.ltIR
d_ltIR_46 :: MAlonzo.Code.Once.IR.T_IR_16
d_ltIR_46
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_396)
-- Once.Surface.Elaborate.leIR
d_leIR_48 :: MAlonzo.Code.Once.IR.T_IR_16
d_leIR_48
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_398)
-- Once.Surface.Elaborate.gtIR
d_gtIR_50 :: MAlonzo.Code.Once.IR.T_IR_16
d_gtIR_50
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_400)
-- Once.Surface.Elaborate.geIR
d_geIR_52 :: MAlonzo.Code.Once.IR.T_IR_16
d_geIR_52
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_402)
-- Once.Surface.Elaborate.eqIR
d_eqIR_54 :: MAlonzo.Code.Once.IR.T_IR_16
d_eqIR_54
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_404)
-- Once.Surface.Elaborate.neIR
d_neIR_56 :: MAlonzo.Code.Once.IR.T_IR_16
d_neIR_56
  = coe
      MAlonzo.Code.Once.IR.C_SigOp_156
      (coe
         MAlonzo.Code.Once.Type.C__'42'__122
         (coe MAlonzo.Code.Once.Type.C_Int_132)
         (coe MAlonzo.Code.Once.Type.C_Int_132))
      (coe
         MAlonzo.Code.Once.Type.C__'43'__124
         (coe MAlonzo.Code.Once.Type.C_Unit_118)
         (coe MAlonzo.Code.Once.Type.C_Unit_118))
      (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_406)
-- Once.Surface.Elaborate.proj
d_proj_64 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_proj_64 ~v0 v1 v2 = du_proj_64 v1 v2
du_proj_64 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_proj_64 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_50
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                          (coe v3)))
                    (coe du_proj_64 (coe v3) (coe v7))
                    (coe MAlonzo.Code.Once.IR.C_fst_44)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.restrictEnv
d_restrictEnv_90 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_restrictEnv_90 ~v0 v1 v2 v3 ~v4 v5
  = du_restrictEnv_90 v1 v2 v3 v5
du_restrictEnv_90 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_restrictEnv_90 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe seq (coe v3) (coe MAlonzo.Code.Once.IR.C_id_22)
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v5 v6 v7
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Context.C__'8849''8759'__290 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v17
                      -> case coe v2 of
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v19 v20
                             -> case coe v13 of
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'z_262
                                    -> coe du_restrictEnv_90 (coe v5) (coe v17) (coe v20) (coe v14)
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'o_264
                                    -> coe
                                         MAlonzo.Code.Once.IR.C__'8728'__30
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                  (coe v5) (coe v17))))
                                         (coe
                                            du_restrictEnv_90 (coe v5) (coe v17) (coe v20)
                                            (coe v14))
                                         (coe MAlonzo.Code.Once.IR.C_fst_44)
                                  MAlonzo.Code.Once.Surface.Context.C_z'8804'm_266
                                    -> coe
                                         MAlonzo.Code.Once.IR.C__'8728'__30
                                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                  (coe v5) (coe v17))))
                                         (coe
                                            du_restrictEnv_90 (coe v5) (coe v17) (coe v20)
                                            (coe v14))
                                         (coe MAlonzo.Code.Once.IR.C_fst_44)
                                  MAlonzo.Code.Once.Surface.Context.C_o'8804'o_268
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_90 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                         (coe MAlonzo.Code.Once.IR.C_snd_50)
                                  MAlonzo.Code.Once.Surface.Context.C_o'8804'm_270
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_90 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                         (coe MAlonzo.Code.Once.IR.C_snd_50)
                                  MAlonzo.Code.Once.Surface.Context.C_m'8804'm_272
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                     (coe v5) (coe v17))))
                                            (coe
                                               du_restrictEnv_90 (coe v5) (coe v17) (coe v20)
                                               (coe v14))
                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                         (coe MAlonzo.Code.Once.IR.C_snd_50)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.projUsed
d_projUsed_160 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
d_projUsed_160 ~v0 v1 v2 = du_projUsed_160 v1 v2
du_projUsed_160 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> MAlonzo.Code.Once.IR.T_IR_16
du_projUsed_160 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Once.IR.C_snd_50
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe du_projUsed_160 (coe v3) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.envˡ
d_env'737'_186 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'737'_186 ~v0 v1 ~v2 v3 v4 = du_env'737'_186 v1 v3 v4
du_env'737'_186 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'737'_186 v0 v1 v2
  = coe
      du_restrictEnv_90 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe v2))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
         (coe v1) (coe v2))
-- Once.Surface.Elaborate.envʳ
d_env'691'_206 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_env'691'_206 ~v0 v1 ~v2 v3 v4 = du_env'691'_206 v1 v3 v4
du_env'691'_206 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_env'691'_206 v0 v1 v2
  = coe
      du_restrictEnv_90 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v1)
         (coe v2))
      (coe v2)
      (coe
         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
         (coe v1) (coe v2))
-- Once.Surface.Elaborate.bindEnv
d_bindEnv_228 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_bindEnv_228 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_bindEnv_228 v5
du_bindEnv_228 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 -> MAlonzo.Code.Once.IR.T_IR_16
du_bindEnv_228 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe MAlonzo.Code.Once.IR.C_fst_44
      MAlonzo.Code.Once.Type.C_One_8 -> coe MAlonzo.Code.Once.IR.C_id_22
      MAlonzo.Code.Once.Type.C_Many_10
        -> coe MAlonzo.Code.Once.IR.C_id_22
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.swap'
d_swap''_246 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swap''_246 ~v0 ~v1 ~v2 = du_swap''_246
du_swap''_246 :: MAlonzo.Code.Once.IR.T_IR_16
du_swap''_246
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
      (coe MAlonzo.Code.Once.IR.C_snd_50)
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Surface.Elaborate.distribute
d_distribute_256 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute_256 v0 v1 v2 ~v3 = du_distribute_256 v0 v1 v2
du_distribute_256 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribute_256 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
         (coe v0))
      (coe du_distrib''_276 (coe v0) (coe v1) (coe v2))
      (coe du_swap''_246)
-- Once.Surface.Elaborate._.curryInlSwap
d_curryInlSwap_270 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInlSwap_270 v0 v1 ~v2 ~v3 = du_curryInlSwap_270 v0 v1
du_curryInlSwap_270 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInlSwap_270 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inl_56) (coe du_swap''_246))
-- Once.Surface.Elaborate._.curryInrSwap
d_curryInrSwap_272 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryInrSwap_272 v0 ~v1 v2 ~v3 = du_curryInrSwap_272 v0 v2
du_curryInrSwap_272 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryInrSwap_272 v0 v1
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
         (coe MAlonzo.Code.Once.IR.C_inr_62) (coe du_swap''_246))
-- Once.Surface.Elaborate._.curryDistrib
d_curryDistrib_274 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryDistrib_274 v0 v1 v2 ~v3 = du_curryDistrib_274 v0 v1 v2
du_curryDistrib_274 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryDistrib_274 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_case_70
      (coe du_curryInlSwap_270 (coe v0) (coe v1))
      (coe du_curryInrSwap_272 (coe v0) (coe v2))
-- Once.Surface.Elaborate._.distrib'
d_distrib''_276 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distrib''_276 v0 v1 v2 ~v3 = du_distrib''_276 v0 v1 v2
du_distrib''_276 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distrib''_276 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
            (coe du_curryDistrib_274 (coe v0) (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.IR.C_fst_44))
         (coe MAlonzo.Code.Once.IR.C_snd_50))
-- Once.Surface.Elaborate.swapIR
d_swapIR_282 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_swapIR_282 ~v0 ~v1 ~v2 = du_swapIR_282
du_swapIR_282 :: MAlonzo.Code.Once.IR.T_IR_16
du_swapIR_282
  = coe
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
      (coe MAlonzo.Code.Once.IR.C_snd_50)
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.Surface.Elaborate.distribIR
d_distribIR_294 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribIR_294 v0 v1 v2 ~v3 = du_distribIR_294 v0 v1 v2
du_distribIR_294 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_distribIR_294 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (coe
         MAlonzo.Code.Once.IRTy.C__'42'__20
         (coe
            MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.C__'43'__22
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))))
         (coe v0))
      (coe MAlonzo.Code.Once.IR.C_apply_92)
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Once.IR.C_case_70
               (coe
                  MAlonzo.Code.Once.IR.C_curry_86
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IR.C_inl_56) (coe du_swapIR_282)))
               (coe
                  MAlonzo.Code.Once.IR.C_curry_86
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v2))
                     (coe MAlonzo.Code.Once.IR.C_inr_62) (coe du_swapIR_282))))
            (coe MAlonzo.Code.Once.IR.C_snd_50))
         (coe MAlonzo.Code.Once.IR.C_fst_44))
-- Once.Surface.Elaborate.compIR
d_compIR_306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_compIR_306 v0 v1 v2 ~v3 = du_compIR_306 v0 v1 v2
du_compIR_306 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_compIR_306 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (coe
            MAlonzo.Code.Once.IRTy.C__'42'__20
            (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
            (coe v1))
         (coe MAlonzo.Code.Once.IR.C_apply_92)
         (coe
            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1)))
               (coe MAlonzo.Code.Once.IR.C_fst_44)
               (coe MAlonzo.Code.Once.IR.C_fst_44))
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                  (coe v0))
               (coe MAlonzo.Code.Once.IR.C_apply_92)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1)))
                     (coe MAlonzo.Code.Once.IR.C_snd_50)
                     (coe MAlonzo.Code.Once.IR.C_fst_44))
                  (coe MAlonzo.Code.Once.IR.C_snd_50)))))
-- Once.Surface.Elaborate.copairIR
d_copairIR_318 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_copairIR_318 v0 v1 v2 ~v3 = du_copairIR_318 v0 v1 v2
du_copairIR_318 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_copairIR_318 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
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
            MAlonzo.Code.Once.IR.C_case_70
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                  (coe v0))
               (coe MAlonzo.Code.Once.IR.C_apply_92)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
                     (coe MAlonzo.Code.Once.IR.C_fst_44)
                     (coe MAlonzo.Code.Once.IR.C_fst_44))
                  (coe MAlonzo.Code.Once.IR.C_snd_50)))
            (coe
               MAlonzo.Code.Once.IR.C__'8728'__30
               (coe
                  MAlonzo.Code.Once.IRTy.C__'42'__20
                  (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2))
                  (coe v1))
               (coe MAlonzo.Code.Once.IR.C_apply_92)
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
                        (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
                     (coe MAlonzo.Code.Once.IR.C_snd_50)
                     (coe MAlonzo.Code.Once.IR.C_fst_44))
                  (coe MAlonzo.Code.Once.IR.C_snd_50))))
         (coe
            du_distribIR_294
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v1) (coe v2)))
            (coe v0) (coe v1)))
-- Once.Surface.Elaborate.forkIR
d_forkIR_330 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_forkIR_330 v0 v1 v2 ~v3 = du_forkIR_330 v0 v1 v2
du_forkIR_330 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_forkIR_330 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
               (coe v0))
            (coe MAlonzo.Code.Once.IR.C_apply_92)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__30
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2)))
                  (coe MAlonzo.Code.Once.IR.C_fst_44)
                  (coe MAlonzo.Code.Once.IR.C_fst_44))
               (coe MAlonzo.Code.Once.IR.C_snd_50)))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2))
               (coe v0))
            (coe MAlonzo.Code.Once.IR.C_apply_92)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__30
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v1))
                     (coe MAlonzo.Code.Once.IRTy.C__'8667'__24 (coe v0) (coe v2)))
                  (coe MAlonzo.Code.Once.IR.C_snd_50)
                  (coe MAlonzo.Code.Once.IR.C_fst_44))
               (coe MAlonzo.Code.Once.IR.C_snd_50))))
-- Once.Surface.Elaborate.curryIR
d_curryIR_342 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_curryIR_342 v0 v1 v2 ~v3 = du_curryIR_342 v0 v1 v2
du_curryIR_342 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
du_curryIR_342 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C_curry_86
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                  (coe v2))
               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Once.IR.C_apply_92)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
               (coe
                  MAlonzo.Code.Once.IR.C__'8728'__30
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                        (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                        (coe v2))
                     (coe v0))
                  (coe MAlonzo.Code.Once.IR.C_fst_44)
                  (coe MAlonzo.Code.Once.IR.C_fst_44))
               (coe
                  MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                  (coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (coe
                        MAlonzo.Code.Once.IRTy.C__'42'__20
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'8667'__24
                           (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v0) (coe v1))
                           (coe v2))
                        (coe v0))
                     (coe MAlonzo.Code.Once.IR.C_snd_50)
                     (coe MAlonzo.Code.Once.IR.C_fst_44))
                  (coe MAlonzo.Code.Once.IR.C_snd_50)))))
-- Once.Surface.Elaborate.cataM
d_cataM_350 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 -> MAlonzo.Code.Once.IR.T_IR_16
d_cataM_350 v0 v1 v2 ~v3 = du_cataM_350 v0 v1 v2
du_cataM_350 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_cataM_350 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.C_curry_86
      (coe
         MAlonzo.Code.Once.IR.C_Cata_108
         (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
            (coe v0) (coe v2))
         (coe
            MAlonzo.Code.Once.IR.C__'8728'__30
            (coe
               MAlonzo.Code.Once.IRTy.C__'42'__20
               (coe
                  MAlonzo.Code.Once.IRTy.C__'8667'__24
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                     (coe
                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1)))
                  (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v1)))
               (coe
                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))))
            (coe MAlonzo.Code.Once.IR.C_apply_92)
            (coe
               MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
               (coe MAlonzo.Code.Once.IR.C_fst_44)
               (coe MAlonzo.Code.Once.IR.C_snd_50))))
-- Once.Surface.Elaborate.elaborate
d_elaborate_370 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate_370 v0 v1 v2 v3 ~v4 v5
  = du_elaborate_370 v0 v1 v2 v3 v5
du_elaborate_370 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborate_370 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v7
        -> coe du_projUsed_160 (coe v1) (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v8 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  seq (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.IR.C_curry_86
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__30
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                    (coe v1) (coe v14))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                    v17 v2))))
                                        (coe
                                           du_elaborate_370
                                           (coe addInt (coe (1 :: Integer)) (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                              (coe v1) (coe v14))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v17
                                              v2)
                                           (coe v16) (coe v13))
                                        (coe MAlonzo.Code.Once.IR.C_fst_44)))
                           MAlonzo.Code.Once.Type.C_One_8
                             -> case coe v8 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_86
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v14))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                        v8 v2))))
                                            (coe
                                               du_elaborate_370
                                               (coe addInt (coe (1 :: Integer)) (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                  (coe v1) (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8
                                                  v2)
                                               (coe v16) (coe v13))
                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_86
                                         (coe
                                            du_elaborate_370
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                               (coe v1) (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8
                                               v2)
                                            (coe v16) (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> case coe v8 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_86
                                         (coe
                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                        (coe v1) (coe v14))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                                                        v8 v2))))
                                            (coe
                                               du_elaborate_370
                                               (coe addInt (coe (1 :: Integer)) (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                  (coe v1) (coe v14))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8
                                                  v2)
                                               (coe v16) (coe v13))
                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_86
                                         (coe
                                            du_elaborate_370
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                               (coe v1) (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8
                                               v2)
                                            (coe v16) (coe v13))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         MAlonzo.Code.Once.IR.C_curry_86
                                         (coe
                                            du_elaborate_370
                                            (coe addInt (coe (1 :: Integer)) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                               (coe v1) (coe v14))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v8
                                               v2)
                                            (coe v16) (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v7 v8 v9 v11 v12 v13
        -> case coe v11 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                    (coe MAlonzo.Code.Once.IR.C_apply_92)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                       (coe
                          du_elaborate_370 (coe v0) (coe v1) (coe v7)
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v3))
                          (coe v12))
                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9)))
                    (coe MAlonzo.Code.Once.IR.C_apply_92)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v7))))
                          (coe
                             du_elaborate_370 (coe v0) (coe v1) (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v3))
                             (coe v12))
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))
                             (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v8))))
                          (coe
                             du_elaborate_370 (coe v0) (coe v1) (coe v8) (coe v9) (coe v13))
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v11) (coe v8)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v11) (coe v8)))))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (coe
                       MAlonzo.Code.Once.IRTy.C__'42'__20
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3)))
                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9)))
                    (coe MAlonzo.Code.Once.IR.C_apply_92)
                    (coe
                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v7))))
                          (coe
                             du_elaborate_370 (coe v0) (coe v1) (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v3))
                             (coe v12))
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))
                             (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v8))))
                          (coe
                             du_elaborate_370 (coe v0) (coe v1) (coe v8) (coe v9) (coe v13))
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v11) (coe v8)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                   (coe v8))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v11) (coe v8)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v7 v8 v9 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                                   (coe v8)))))
                       (coe
                          MAlonzo.Code.Once.IR.C__'8728'__30
                          (coe
                             MAlonzo.Code.Once.IRTy.C__'42'__20
                             (coe
                                MAlonzo.Code.Once.IRTy.C__'8667'__24
                                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9))
                                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15)))
                             (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9)))
                          (coe MAlonzo.Code.Once.IR.C_apply_92)
                          (coe
                             MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__30
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                         (coe v7))))
                                (coe
                                   du_elaborate_370 (coe v0) (coe v1) (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                         (coe MAlonzo.Code.Once.Type.C_eff_36))
                                      (coe v15))
                                   (coe v11))
                                (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                             (coe
                                MAlonzo.Code.Once.IR.C__'8728'__30
                                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                         (coe v8))))
                                (coe
                                   du_elaborate_370 (coe v0) (coe v1) (coe v8) (coe v9) (coe v12))
                                (coe du_env'691'_206 (coe v1) (coe v7) (coe v8)))))
                       (coe MAlonzo.Code.Once.IR.C_fst_44))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v7 v8 v11 v12
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
               -> coe
                    MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                (coe v7))))
                       (coe
                          du_elaborate_370 (coe v0) (coe v1) (coe v7) (coe v13) (coe v11))
                       (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                (coe v8))))
                       (coe
                          du_elaborate_370 (coe v0) (coe v1) (coe v8) (coe v14) (coe v12))
                       (coe du_env'691'_206 (coe v1) (coe v7) (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9)))
             (coe MAlonzo.Code.Once.IR.C_fst_44)
             (coe
                du_elaborate_370 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v3) (coe v9))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v8 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v8))
                (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v3)))
             (coe MAlonzo.Code.Once.IR.C_snd_50)
             (coe
                du_elaborate_370 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v8) (coe v3))
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v11))
                    (coe MAlonzo.Code.Once.IR.C_inl_56)
                    (coe
                       du_elaborate_370 (coe v0) (coe v1) (coe v2) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                    (coe MAlonzo.Code.Once.IR.C_inr_62)
                    (coe
                       du_elaborate_370 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'43'__22
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12)))
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13))))
             (coe
                MAlonzo.Code.Once.IR.C_case_70
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v10 v8))))
                   (coe
                      du_elaborate_370 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v12))
                      (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v10 v8)
                      (coe v3) (coe v16))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__30
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                  (coe v8))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12)))
                      (coe du_bindEnv_228 (coe v10))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__30
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                        (coe v8) (coe v9)))))
                            (coe
                               du_restrictEnv_90 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                                  (coe v9))
                               (coe v8)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
                                  (coe v8) (coe v9)))
                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                         (coe MAlonzo.Code.Once.IR.C_snd_50))))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v13))
                            (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v9))))
                   (coe
                      du_elaborate_370 (coe addInt (coe (1 :: Integer)) (coe v0))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v13))
                      (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v9)
                      (coe v3) (coe v17))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__30
                      (coe
                         MAlonzo.Code.Once.IRTy.C__'42'__20
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                  (coe v9))))
                         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13)))
                      (coe du_bindEnv_228 (coe v11))
                      (coe
                         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                         (coe
                            MAlonzo.Code.Once.IR.C__'8728'__30
                            (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                        (coe v8) (coe v9)))))
                            (coe
                               du_restrictEnv_90 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                                  (coe v9))
                               (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
                                  (coe v8) (coe v9)))
                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                         (coe MAlonzo.Code.Once.IR.C_snd_50)))))
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (coe
                   MAlonzo.Code.Once.IRTy.C__'42'__20
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))))
                   (coe
                      MAlonzo.Code.Once.IRTy.C__'43'__22
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13))))
                (coe
                   du_distribute_256
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                   (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v13)))
                (coe
                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                   (coe
                      du_restrictEnv_90 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                            (coe v9)))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                         (coe v7)
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                            (coe v9))))
                   (coe
                      MAlonzo.Code.Once.IR.C__'8728'__30
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                               (coe v7))))
                      (coe
                         du_elaborate_370 (coe v0) (coe v1) (coe v7)
                         (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v12) (coe v13))
                         (coe v15))
                      (coe
                         du_restrictEnv_90 (coe v1)
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))
                         (coe v7)
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                            (coe v7)
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v8)
                               (coe v9)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe MAlonzo.Code.Once.IR.C_terminal_74
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v9
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.IRTy.C_Void_18)
             (coe MAlonzo.Code.Once.IR.C_initial_78)
             (coe
                du_elaborate_370 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v7 v8 v9 v10 v12 v13
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    du_elaborate_370 (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v10))
                    (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v9 v8)
                    (coe v3) (coe v13)
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v10))
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v9 v8))))
                    (coe
                       du_elaborate_370 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v10))
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v9 v8)
                       (coe v3) (coe v13))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v8))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10)))
                       (coe du_bindEnv_228 (coe v9))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                   (coe v7)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                   (coe v7))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__30
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                      (coe v7))))
                             (coe
                                du_elaborate_370 (coe v0) (coe v1) (coe v7) (coe v10) (coe v12))
                             (coe
                                du_restrictEnv_90 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                      (coe v7)))
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v9) (coe v7)))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v9) (coe v7))))))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__30
                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v10))
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v9 v8))))
                    (coe
                       du_elaborate_370 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v10))
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v9 v8)
                       (coe v3) (coe v13))
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (coe
                          MAlonzo.Code.Once.IRTy.C__'42'__20
                          (coe
                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                   (coe v8))))
                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10)))
                       (coe du_bindEnv_228 (coe v9))
                       (coe
                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                          (coe
                             du_restrictEnv_90 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                   (coe v7)))
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                   (coe v7))))
                          (coe
                             MAlonzo.Code.Once.IR.C__'8728'__30
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                      (coe v7))))
                             (coe
                                du_elaborate_370 (coe v0) (coe v1) (coe v7) (coe v10) (coe v12))
                             (coe
                                du_restrictEnv_90 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                      (coe v7)))
                                (coe v7)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v9)
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v9) (coe v7)))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                      (coe v7))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                         (coe v9) (coe v7))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v7
        -> coe du_intLit_8 (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v7
        -> coe du_strLit_14 (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v7
        -> coe du_floatLit_20 (coe v7)
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_addIR_24
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_subIR_26
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_mulIR_28
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_faddIR_34
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fsubIR_36
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fmulIR_38
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Float_32)
                (coe MAlonzo.Code.Once.IRTy.C_Float_32))
             d_fdivIR_40
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.IRTy.C_Int_30) d_i2fIR_42
             (coe
                du_elaborate_370 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_divIR_30
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_modIR_32
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe MAlonzo.Code.Once.IRTy.C_Int_30) d_negIR_44
             (coe
                du_elaborate_370 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v8))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_ltIR_46
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_leIR_48
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_gtIR_50
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_geIR_52
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_eqIR_54
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (coe
                MAlonzo.Code.Once.IRTy.C__'42'__20
                (coe MAlonzo.Code.Once.IRTy.C_Int_30)
                (coe MAlonzo.Code.Once.IRTy.C_Int_30))
             d_neIR_56
             (coe
                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v7))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v7)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9))
                   (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                (coe
                   MAlonzo.Code.Once.IR.C__'8728'__30
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                            (coe v8))))
                   (coe
                      du_elaborate_370 (coe v0) (coe v1) (coe v8)
                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10))
                   (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    du_elaborate_370 (coe v0) (coe v1) (coe v2)
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v13))
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v8 v9
        -> let v10
                 = coe
                     MAlonzo.Code.Once.IR.C__'8728'__30
                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                        (coe MAlonzo.Code.Once.Type.C_Unit_118))
                     (coe
                        MAlonzo.Code.Once.IR.C_SigOp_156
                        (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                           (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v3) (coe v8)
                           (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                           (coe v9)))
                     (coe MAlonzo.Code.Once.IR.C_terminal_74) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                  -> case coe v12 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                         -> case coe v14 of
                              MAlonzo.Code.Once.Type.C_Zero_6
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v19 v20
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_86
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                  (coe MAlonzo.Code.Once.Type.C_Unit_118))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_156
                                                  (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                                                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                     (coe v13) (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                                     (coe v20)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_50))
                                     _ -> coe v10
                              MAlonzo.Code.Once.Type.C_One_8
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v19 v20
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_86
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_156 (coe v11)
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                     (coe v11) (coe v13) (coe v12) (coe v8)
                                                     (coe v19) (coe v20)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_50))
                                     _ -> coe v10
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v9 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v19 v20
                                       -> coe
                                            MAlonzo.Code.Once.IR.C_curry_86
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_SigOp_156 (coe v11)
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                     (coe v11) (coe v13) (coe v12) (coe v8)
                                                     (coe v19) (coe v20)))
                                               (coe MAlonzo.Code.Once.IR.C_snd_50))
                                     _ -> coe v10
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v8
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                (coe MAlonzo.Code.Once.Type.C_Unit_118))
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_156
                (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v3)
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                   (coe v3) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v7
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                (coe MAlonzo.Code.Once.Type.C_Unit_118))
             (coe
                MAlonzo.Code.Once.IR.C_SigOp_156
                (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v3)
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                   (coe v3) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7))))
             (coe MAlonzo.Code.Once.IR.C_terminal_74)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414 v10
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.IR.C_curry_86
                    (coe
                       MAlonzo.Code.Once.IR.C__'8728'__30
                       (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v11)) v10
                       (coe MAlonzo.Code.Once.IR.C_snd_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__30
             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v8)) v10
             (coe
                MAlonzo.Code.Once.IR.C__'8728'__30
                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                         (coe v7))))
                (coe
                   du_elaborate_370 (coe v0) (coe v1) (coe v7) (coe v8) (coe v11))
                (coe
                   du_restrictEnv_90 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                      (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                   (coe v7)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                      (coe v7)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                         (coe v7))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))))))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_444 v7 v8 v10 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10))))
                           (coe
                              du_compIR_306
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v10))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                          (coe v7))))
                                 (coe
                                    du_elaborate_370 (coe v0) (coe v1) (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                       (coe v17))
                                    (coe v13))
                                 (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                          (coe v8))))
                                 (coe
                                    du_elaborate_370 (coe v0) (coe v1) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                       (coe v10))
                                    (coe v14))
                                 (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_462 v7 v8 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v18 v19
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__30
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'42'__20
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.C__'8667'__24
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v19))
                                        (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17))))
                                  (coe
                                     du_copairIR_318
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v19))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                                  (coe
                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__30
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                 (coe v1) (coe v7))))
                                        (coe
                                           du_elaborate_370 (coe v0) (coe v1) (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v18)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                              (coe v17))
                                           (coe v13))
                                        (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                                     (coe
                                        MAlonzo.Code.Once.IR.C__'8728'__30
                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                 (coe v1) (coe v8))))
                                        (coe
                                           du_elaborate_370 (coe v0) (coe v1) (coe v8)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe v19)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                              (coe v17))
                                           (coe v14))
                                        (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_478 v7 v8 v12 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v14))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v14))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18))))
                           (coe
                              du_forkIR_330
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v14))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v18)))
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                          (coe v7))))
                                 (coe
                                    du_elaborate_370 (coe v0) (coe v1) (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                       (coe v17))
                                    (coe v12))
                                 (coe du_env'737'_186 (coe v1) (coe v7) (coe v8)))
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
                                          (coe v8))))
                                 (coe
                                    du_elaborate_370 (coe v0) (coe v1) (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                       (coe v18))
                                    (coe v13))
                                 (coe du_env'691'_206 (coe v1) (coe v7) (coe v8))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_492 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'8667'__24
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15)))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                           (coe
                              du_curryIR_342
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v15))
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v17)))
                           (coe
                              du_elaborate_370 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                 (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v12) (coe v15))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v17))
                              (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_504 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.IR.C__'8728'__30
                                  (coe
                                     MAlonzo.Code.Once.IRTy.C__'8667'__24
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v15)
                                           (coe v14)))
                                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v14)))
                                  (coe du_cataM_350 (coe v15) (coe v14) (coe v10))
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                              (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                 (coe (0 :: Integer))))))
                                     (coe
                                        du_elaborate_370 (coe (0 :: Integer))
                                        (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                           (coe (0 :: Integer)))
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                           (coe
                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                              (coe v15) (coe v14))
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                                           (coe v14))
                                        (coe v11))
                                     (coe MAlonzo.Code.Once.IR.C_terminal_74))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_516 v10 v11
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v17
                             -> coe
                                  MAlonzo.Code.Once.IR.C_curry_86
                                  (coe
                                     MAlonzo.Code.Once.IR.C__'8728'__30
                                     (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v12))
                                     (coe
                                        MAlonzo.Code.Once.IR.C_Ana_128
                                        (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                           (coe v17) (coe v10))
                                        (coe
                                           MAlonzo.Code.Once.IR.C__'8728'__30
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'42'__20
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.C__'8667'__24
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                    (coe v12))
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                    (coe
                                                       MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                       (coe v17) (coe v12))))
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                 (coe v12)))
                                           (coe MAlonzo.Code.Once.IR.C_apply_92)
                                           (coe
                                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                              (coe
                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Context.du__'8638'__234
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                             (coe (0 :: Integer))))))
                                                 (coe
                                                    du_elaborate_370 (coe (0 :: Integer))
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                       (coe (0 :: Integer)))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v12)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                          (coe v17) (coe v12)))
                                                    (coe v11))
                                                 (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                              (coe MAlonzo.Code.Once.IR.C_id_22))))
                                     (coe MAlonzo.Code.Once.IR.C_snd_50))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.eraseCtx
d_eraseCtx_920 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_eraseCtx_920 ~v0 v1 ~v2 v3 = du_eraseCtx_920 v1 v3
du_eraseCtx_920 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_eraseCtx_920 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe seq (coe v1) (coe MAlonzo.Code.Once.IR.C_id_22)
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__30
                           (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                 (coe v3)))
                           (coe du_eraseCtx_920 (coe v3) (coe v8))
                           (coe MAlonzo.Code.Once.IR.C_fst_44)
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__30
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                    (coe v3)))
                              (coe du_eraseCtx_920 (coe v3) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_44))
                           (coe MAlonzo.Code.Once.IR.C_snd_50)
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                           (coe
                              MAlonzo.Code.Once.IR.C__'8728'__30
                              (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                    (coe v3)))
                              (coe du_eraseCtx_920 (coe v3) (coe v8))
                              (coe MAlonzo.Code.Once.IR.C_fst_44))
                           (coe MAlonzo.Code.Once.IR.C_snd_50)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Surface.Elaborate.elaborateFull
d_elaborateFull_962 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborateFull_962 v0 v1 v2 v3 ~v4 v5
  = du_elaborateFull_962 v0 v1 v2 v3 v5
du_elaborateFull_962 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_elaborateFull_962 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.C__'8728'__30
      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52
         (coe
            MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8638'__234 (coe v1)
               (coe v2))))
      (coe du_elaborate_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe du_eraseCtx_920 (coe v1) (coe v2))
-- Once.Surface.Elaborate.elaborate-default
d_elaborate'45'default_980 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_elaborate'45'default_980 v0 v1 v2 v3
  = coe du_elaborateFull_962 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Surface.Elaborate.distribute-default
d_distribute'45'default_988 ::
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_distribute'45'default_988 v0 v1 v2
  = coe du_distribute_256 (coe v0) (coe v1) (coe v2)
