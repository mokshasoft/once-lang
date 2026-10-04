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

module MAlonzo.Code.Once.Adequacy.TableCall where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.TableCall.tableEnv-skip
d_tableEnv'45'skip_22 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableEnv'45'skip_22 = erased
-- Once.Adequacy.TableCall.tableEnv-hit
d_tableEnv'45'hit_84 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableEnv'45'hit_84 = erased
-- Once.Adequacy.TableCall.abiT
d_abiT_158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_abiT_158 ~v0 ~v1 v2 v3 = du_abiT_158 v2 v3
du_abiT_158 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_abiT_158 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                       (\ v7 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                            (coe v1) (coe (\ v8 -> coe v8 v7))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_136 -> coe v1
      MAlonzo.Code.Once.Type.C_rigid_138 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TableCall.uncurry-app
d_uncurry'45'app_244 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uncurry'45'app_244 = erased
-- Once.Adequacy.TableCall.abi
d_abi_264 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi_264 = erased
