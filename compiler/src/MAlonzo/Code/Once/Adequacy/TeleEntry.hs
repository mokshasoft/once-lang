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

module MAlonzo.Code.Once.Adequacy.TeleEntry where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Adequacy.GradedRelation
import qualified MAlonzo.Code.Once.Adequacy.MeaningBridge
import qualified MAlonzo.Code.Once.Adequacy.TableCall
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.GradedOps
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.TeleEntry.φ
d_φ_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_φ_10 ~v0 v1 = du_φ_10 v1
du_φ_10 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
du_φ_10 v0
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_540 (coe v0)
-- Once.Adequacy.TeleEntry._.RelGM
d_RelGM_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGM_14 = erased
-- Once.Adequacy.TeleEntry._.RelGT
d_RelGT_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 -> ()
d_RelGT_16 = erased
-- Once.Adequacy.TeleEntry._.RelGV
d_RelGV_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny -> ()
d_RelGV_20 = erased
-- Once.Adequacy.TeleEntry._.abiT
d_abiT_26 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_abiT_26 ~v0 ~v1 = du_abiT_26
du_abiT_26 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_abiT_26 = coe MAlonzo.Code.Once.Adequacy.TableCall.du_abiT_158
-- Once.Adequacy.TeleEntry.returns-of
d_returns'45'of_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_returns'45'of_36 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_returns'45'of_36 v4 v5
du_returns'45'of_36 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_returns'45'of_36 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_1088 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEntry.abi-many
d_abi'45'many_72 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  () ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'many_72 = erased
-- Once.Adequacy.TeleEntry.abi-zero
d_abi'45'zero_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abi'45'zero_96 = erased
-- Once.Adequacy.TeleEntry.abi-rel
d_abi'45'rel_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_abi'45'rel_106 ~v0 ~v1 v2 ~v3 v4 v5 = du_abi'45'rel_106 v2 v4 v5
du_abi'45'rel_106 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
du_abi'45'rel_106 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe v2
      MAlonzo.Code.Once.Type.C_Void_122 -> coe v2
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4 -> coe v2
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4 -> coe v2
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> coe
                    seq (coe v6)
                    (let v8 = coe du_returns'45'of_36 (coe v1) (coe v2) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                            -> case coe v10 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                   -> coe
                                        MAlonzo.Code.Once.Adequacy.GradedRelation.du_RelGT'45'return_162
                                        (coe v12)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4 -> coe v2
      MAlonzo.Code.Once.Type.C_Int_134 -> coe v2
      MAlonzo.Code.Once.Type.C_Float_136 -> coe v2
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.TeleEntry.ffi-entry
d_ffi'45'entry_310 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_ffi'45'entry_310 v0 v1 v2 v3 v4 v5 ~v6
  = du_ffi'45'entry_310 v0 v1 v2 v3 v4 v5
du_ffi'45'entry_310 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
du_ffi'45'entry_310 v0 v1 v2 v3 v4 v5
  = coe
      du_abi'45'rel_106 (coe v4)
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe du_ρ_328 (coe v0) (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe
               MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)))
         (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
         (coe du_ir_330 (coe v3) (coe v4) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Adequacy.MeaningBridge.du_sigop'45'ref'45'bridge_870
         (coe v0) (coe v4) (coe v1)
         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v3)) (coe v5))
-- Once.Adequacy.TeleEntry._.ref
d_ref_326 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_ref_326 v0 v1 ~v2 v3 v4 v5 ~v6 = du_ref_326 v0 v1 v3 v4 v5
du_ref_326 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 -> AgdaAny
du_ref_326 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.GradedOps.du_sigOpRef'7515'_514
      (coe v3) (coe v0)
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.d_sig_464 (coe v1))
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.d_impl_466 (coe v1))
      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v2)) (coe v4)
-- Once.Adequacy.TeleEntry._.ρ
d_ρ_328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
d_ρ_328 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 = du_ρ_328 v0 v1 v2
du_ρ_328 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
du_ρ_328 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
      (coe du_φ_10 (coe v1)) (coe v2)
-- Once.Adequacy.TeleEntry._.ir
d_ir_330 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_458 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_ir_330 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 = du_ir_330 v3 v4 v5
du_ir_330 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_ir_330 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_996
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe
         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
         (coe (0 :: Integer)))
      (coe v1)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
         (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) v2)
