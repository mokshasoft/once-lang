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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.TeleWalk
import qualified MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Telescope
import qualified MAlonzo.Code.Once.Lang.Core.Translate
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Metatheory.Trace
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Trace

-- Once.Adequacy.CoreBridge.typedSig-ef
d_typedSig'45'ef_14 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
             MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedSig
d_typedSig_24 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
                       MAlonzo.Code.Once.Parser.d_extractFunctions_632
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                       (coe v1))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedProgram-ef
d_typedProgram'45'ef_38 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
d_typedProgram'45'ef_38 ~v0 ~v1 v2 v3 v4
  = du_typedProgram'45'ef_38 v2 v3 v4
du_typedProgram'45'ef_38 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
du_typedProgram'45'ef_38 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Translate.d_toProgram'8320'_1440
                    (coe v3) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typedProgram
d_typedProgram_52 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
d_typedProgram_52 ~v0 v1 = du_typedProgram_52 v1
du_typedProgram_52 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
du_typedProgram_52 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_typedProgram'45'ef_38
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions_632
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                       (coe v1))
                    (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge.typed-sig-ef
d_typed'45'sig'45'ef_66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typed'45'sig'45'ef_66 = erased
-- Once.Adequacy.CoreBridge.typed-sig
d_typed'45'sig_78 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_typed'45'sig_78 = erased
-- Once.Adequacy.CoreBridge.implFor
d_implFor_88 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242
d_implFor_88 ~v0 ~v1 v2 = du_implFor_88 v2
du_implFor_88 ::
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242
du_implFor_88 v0 = coe v0
-- Once.Adequacy.CoreBridge.interp-subst
d_interp'45'subst_102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interp'45'subst_102 = erased
-- Once.Adequacy.CoreBridge.trIRAt
d_trIRAt_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_trIRAt_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceTr.du_trT'8734'_122 (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
            (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v1))
            (coe v2))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
         (coe v3) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Adequacy.CoreBridge.agree-at
d_agree'45'at_126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_agree'45'at_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_agree'45'at_126 v8
du_agree'45'at_126 ::
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_agree'45'at_126 v0 = coe v0
-- Once.Adequacy.CoreBridge.core-ef-tr
d_core'45'ef'45'tr_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_core'45'ef'45'tr_146 v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 v8 v9 ~v10 v11
  = du_core'45'ef'45'tr_146 v0 v3 v4 v5 v8 v9 v11
du_core'45'ef'45'tr_146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_core'45'ef'45'tr_146 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             MAlonzo.Code.Once.Metatheory.Trace.du_WB'45'sym_82 erased
             (coe
                MAlonzo.Code.Once.Denotation.TraceTr.du_RelS'45'tr_568
                (coe
                   MAlonzo.Code.Once.Lang.Trace.C_interp_192
                   (coe
                      MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v3) (coe v1))
                   (coe v6))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Once.Lang.Core.Telescope.d_runCore_150
                   (coe
                      MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v3) (coe v1))
                   (coe v0)
                   (coe
                      MAlonzo.Code.Once.Lang.Core.Translate.d_toProgram_892
                      (coe
                         MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v3) (coe v1))
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_'91''93'_830)
                      (coe
                         MAlonzo.Code.Once.Lang.Module.C_scope_20
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                         (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_104)
                         (coe
                            MAlonzo.Code.Once.Compile.d_telePolys_410
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      (coe v3) (coe MAlonzo.Code.Once.Lang.Core.Telescope.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_68)
                      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_92)
                      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_118) erased
                      (coe v1) (coe v8) (coe (\ v9 v10 -> v10)))
                   (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Denotation.Program.d_tableEnv_26 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Adequacy.TeleWalk.du_φ_14
                         (coe
                            MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v3) (coe v1))
                         (coe v6))
                      (coe
                         MAlonzo.Code.Once.Compile.d_tableOf'45'go_1040
                         (coe
                            MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_340
                            (coe v3) (coe v4))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                   (coe
                      MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                   (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreBridge._.I′
d_I'8242'_168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242
d_I'8242'_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_I'8242'_168 v10
du_I'8242'_168 ::
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242
du_I'8242'_168 v0 = coe v0
-- Once.Adequacy.CoreBridge._.P
d_P_170 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
d_P_170 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_P_170 v2 v3 v5
du_P_170 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Core.Telescope.T_Program_106
du_P_170 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Translate.d_toProgram_892
      (coe
         MAlonzo.Code.Once.Lang.Module.du_teleSig_116 (coe v0) (coe v1))
      (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Lang.Core.PolyTy.C_'91''93'_830)
      (coe
         MAlonzo.Code.Once.Lang.Module.C_scope_20
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe v0) (coe MAlonzo.Code.Once.Lang.Core.Telescope.C_'91''93'_16)
      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_68)
      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_92)
      (coe MAlonzo.Code.Once.Lang.Core.Translate.C_'91''93'_118) erased
      (coe v1) (coe v2) (coe (\ v3 v4 -> v4))
-- Once.Adequacy.CoreBridge._.inv₀
d_inv'8320'_194 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_50 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120
d_inv'8320'_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du_inv'8320'_194
du_inv'8320'_194 ::
  MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.T_Inv_120
du_inv'8320'_194
  = coe
      MAlonzo.Code.Once.Adequacy.TeleWalk.Invariant.C_constructor_166
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
-- Once.Adequacy.CoreBridge.program-core-tr
d_program'45'core'45'tr_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
d_program'45'core'45'tr_222 v0 v1 v2 v3 v4 v5 ~v6
  = du_program'45'core'45'tr_222 v0 v1 v2 v3 v4 v5
du_program'45'core'45'tr_222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Spec.Trace.T__'8776''7511''10216'_'10217'__86
du_program'45'core'45'tr_222 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Adequacy.FunBundle.du_node'45'ef_1198
              (coe
                 MAlonzo.Code.Once.Parser.d_guardDistinct_542
                 (coe
                    MAlonzo.Code.Once.Parser.d_thenExtract_626
                    (coe
                       MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v1))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
                       (coe
                          MAlonzo.Code.Once.Parser.d_sigsFirst_622
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              du_core'45'ef'45'tr_146 (coe v0) (coe v2) (coe v3) (coe v7)
                              (coe v11) (coe v5) (coe v4)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CoreBridge._.ι
d_ι_264 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
d_ι_264 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_ι_264 v0 v10
du_ι_264 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182
du_ι_264 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Trace.C_interp_192
      (coe MAlonzo.Code.Once.Lang.Module.d_moduleSig_132 (coe v0))
      (coe v1)
-- Once.Adequacy.CoreBridge._.fe
d_fe_266 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fe_266 = erased
