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

module MAlonzo.Code.Once.Adequacy.CoreBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.Telescope
import qualified MAlonzo.Code.Once.Spec.Core.Translate
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CoreBridge.typedSig-ef
d_typedSig'45'ef_14 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_typedSig'45'ef_14 ~v0 ~v1 v2 v3 = du_typedSig'45'ef_14 v2 v3
du_typedSig'45'ef_14 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_typedSig'45'ef_14 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Once.Spec.Module.du_teleSig_116 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedSig
d_typedSig_24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_typedSig_24 ~v0 v1 = du_typedSig_24 v1
du_typedSig_24 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_typedSig_24 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_typedSig'45'ef_14
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions_572
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                       (coe v1))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedProgram-ef
d_typedProgram'45'ef_38 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_typedProgram'45'ef_38 ~v0 ~v1 v2 v3 v4
  = du_typedProgram'45'ef_38 v2 v3 v4
du_typedProgram'45'ef_38 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
du_typedProgram'45'ef_38 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Translate.d_toProgram'8320'_1402
                    (coe v3) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedProgram
d_typedProgram_52 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
d_typedProgram_52 ~v0 v1 = du_typedProgram_52 v1
du_typedProgram_52 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Core.Telescope.T_Program_100
du_typedProgram_52 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_typedProgram'45'ef_38
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions_572
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                       (coe v1))
                    (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typed-sig-ef
d_typed'45'sig'45'ef_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typed'45'sig'45'ef_66 = erased
-- Once.Adequacy.CoreBridge.typed-sig
d_typed'45'sig_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typed'45'sig_78 = erased
-- Once.Adequacy.CoreBridge.implFor
d_implFor_88 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292
d_implFor_88 ~v0 ~v1 v2 = du_implFor_88 v2
du_implFor_88 ::
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292
du_implFor_88 v0 = coe v0
-- Once.Adequacy.CoreBridge.interp-subst
d_interp'45'subst_102 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interp'45'subst_102 = erased
-- Once.Adequacy.CoreBridge.runIRAt
d_runIRAt_106 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_124]
d_runIRAt_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_542 (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
            (coe
               MAlonzo.Code.Once.Denotation.TraceMonad.d_pureHalf_350 (coe v1))
            (coe v2))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Type.C_Unit_120))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Type.C_Unit_120))
         (coe MAlonzo.Code.Once.Compile.d_mainCall_814)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe v3)
-- Once.Adequacy.CoreBridge.core-ef
d_core'45'ef_130 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_core'45'ef_130 = erased
-- Once.Adequacy.CoreBridge._.I′
d_I'8242'_150 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> MAlonzo.Code.Once.Spec.Contract.T_Impl_292
d_I'8242'_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_I'8242'_150 v8
du_I'8242'_150 ::
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292
du_I'8242'_150 v0 = coe v0
-- Once.Adequacy.CoreBridge._.inv₀
d_inv'8320'_170 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_84
d_inv'8320'_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_inv'8320'_170
du_inv'8320'_170 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_84
du_inv'8320'_170
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.C_constructor_130
      erased erased
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (coe
         (\ v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) erased)))
-- Once.Adequacy.CoreBridge.program-core
d_program'45'core_200 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_program'45'core_200 = erased
-- Once.Adequacy.CoreBridge._.ι
d_ι_246 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268
d_ι_246 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11
  = du_ι_246 v0 v10
du_ι_246 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_Interp_268
du_ι_246 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.C_interp_278
      (coe MAlonzo.Code.Once.Spec.Module.d_moduleSig_132 (coe v0))
      (coe v1)
-- Once.Adequacy.CoreBridge._.ir≡
d_ir'8801'_248 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'8801'_248 = erased
