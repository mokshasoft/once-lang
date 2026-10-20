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

module MAlonzo.Code.Once.Adequacy.SourceTrace where

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
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.MachineTrace
import qualified MAlonzo.Code.Once.Adequacy.RewriteLinked
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Behavior
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.TraceTr
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Trace
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.SourceTrace.linkedAt-rewrite
d_linkedAt'45'rewrite_14 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny
d_linkedAt'45'rewrite_14 v0 v1 v2 v3 v4
  = case coe v0 of
      (:) v5 v6
        -> coe
             du_linkedAt'45'rewrite'45'at_32 (coe v6) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v5))
                (coe v1))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v5))
                (coe v2))
             (coe
                MAlonzo.Code.Once.IRTy.d__'8799'IRTy__196
                (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v5))
                (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.linkedAt-rewrite-at
d_linkedAt'45'rewrite'45'at_32 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
d_linkedAt'45'rewrite'45'at_32 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_linkedAt'45'rewrite'45'at_32 v1 v2 v3 v4 v5 v6 v7 v8
du_linkedAt'45'rewrite'45'at_32 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
du_linkedAt'45'rewrite'45'at_32 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (case coe v6 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                               else coe
                                                      seq (coe v13)
                                                      (coe
                                                         d_linkedAt'45'rewrite_14 (coe v0) (coe v1)
                                                         (coe v2) (coe v3) (coe v7))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v11)
                                     (coe
                                        d_linkedAt'45'rewrite_14 (coe v0) (coe v1) (coe v2) (coe v3)
                                        (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v9)
                    (coe
                       d_linkedAt'45'rewrite_14 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.linked-retable
d_linked'45'retable_110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_linked'45'retable_110 ~v0 v1 v2 v3 v4 v5
  = du_linked'45'retable_110 v1 v2 v3 v4 v5
du_linked'45'retable_110 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
du_linked'45'retable_110 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_linked'45'retable_110 (coe v0) (coe v6) (coe v2) (coe v8)
                       (coe v10))
                    (coe
                       du_linked'45'retable_110 (coe v0) (coe v1) (coe v6) (coe v9)
                       (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_linked'45'retable_110 (coe v0) (coe v1) (coe v10) (coe v8)
                              (coe v12))
                           (coe
                              du_linked'45'retable_110 (coe v0) (coe v1) (coe v11) (coe v9)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_linked'45'retable_110 (coe v0) (coe v10) (coe v2) (coe v8)
                              (coe v12))
                           (coe
                              du_linked'45'retable_110 (coe v0) (coe v11) (coe v2) (coe v9)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_curry_84 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
               -> coe
                    du_linked'45'retable_110 (coe v0)
                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v9))
                    (coe v10) (coe v8) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_In_94 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           du_linked'45'retable_110 (coe v0)
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v12) (coe v2)))
                           (coe v2) (coe v9) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v6
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_Ana_122 v6 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           du_linked'45'retable_110 (coe v0) (coe v1)
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_80 (coe v12) (coe v11))
                           (coe v9) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v8
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    du_linked'45'retable_110 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v2) (coe v10))
                    (coe v8) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.IR.C_SigOp_140 v5 v6 v7 -> coe v4
      MAlonzo.Code.Once.IR.C_Call_146 v7
        -> coe
             d_linkedAt'45'rewrite_14 (coe v0) (coe v7) (coe v1) (coe v2)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.all-rewrite-linked
d_all'45'rewrite'45'linked_216 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'rewrite'45'linked_216 ~v0 v1 v2 v3
  = du_all'45'rewrite'45'linked_216 v1 v2 v3
du_all'45'rewrite'45'linked_216 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'45'rewrite'45'linked_216 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       MAlonzo.Code.Once.Adequacy.RewriteLinked.du_rewrite'45'ir'45'linked_350
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                       (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                       (coe
                          du_linked'45'retable_110 (coe v0)
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
                          (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v3))
                          (coe v7)))
                    (coe du_all'45'rewrite'45'linked_216 (coe v0) (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.rewrite-program-linked
d_rewrite'45'program'45'linked_234 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rewrite'45'program'45'linked_234 ~v0 v1 v2
  = du_rewrite'45'program'45'linked_234 v1 v2
du_rewrite'45'program'45'linked_234 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_rewrite'45'program'45'linked_234 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.RewriteLinked.du_rewrite'45'ir'45'linked_350
                (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                (coe MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v0))
                (coe
                   du_linked'45'retable_110
                   (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0))
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v0))
                   (coe v2)))
             (coe
                du_all'45'rewrite'45'linked_216
                (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0))
                (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.⟦_⟧IRᵗ
d_'10214'_'10215'IR'7511'_242 ::
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Spec.Trace.T_Tr_18
d_'10214'_'10215'IR'7511'_242 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             MAlonzo.Code.Once.Denotation.TraceTr.du_trT'8734'_122 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                MAlonzo.Code.Once.Denotation.Program.d_runIR_398 (coe v1)
                (coe MAlonzo.Code.Once.Lang.Trace.d_pureHalf_262 (coe v2))
                (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Adequacy.MachineTrace.d_silentTr_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.eitherToMaybe
d_eitherToMaybe_250 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_eitherToMaybe_250 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-aux
d_srcToModule'45'aux_254 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_srcToModule'45'aux_254 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             d_eitherToMaybe_250
             (coe
                MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveImports_1074
                (coe v0) (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule
d_srcToModule_262 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32
d_srcToModule_262 v0
  = coe
      d_srcToModule'45'aux_254
      (coe
         MAlonzo.Code.Once.Denotation.Behavior.d_srcImports_50 (coe v0))
      (coe
         d_eitherToMaybe_250
         (coe
            MAlonzo.Code.Once.Parser.d_parseStrict_72
            (coe MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v0))))
-- Once.Adequacy.SourceTrace.srcToModule-just
d_srcToModule'45'just_272 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_srcToModule'45'just_272 = erased
-- Once.Adequacy.SourceTrace.eitherToMaybe-inv
d_eitherToMaybe'45'inv_296 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eitherToMaybe'45'inv_296 = erased
-- Once.Adequacy.SourceTrace.srcToModule-inv-p
d_srcToModule'45'inv'45'p_314 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv'45'p_314 ~v0 v1 ~v2 ~v3
  = du_srcToModule'45'inv'45'p_314 v1
du_srcToModule'45'inv'45'p_314 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv'45'p_314 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.SourceTrace.srcToModule-inv
d_srcToModule'45'inv_334 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_srcToModule'45'inv_334 v0 ~v1 ~v2 = du_srcToModule'45'inv_334 v0
du_srcToModule'45'inv_334 ::
  MAlonzo.Code.Once.Denotation.Behavior.T_Source_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_srcToModule'45'inv_334 v0
  = coe
      du_srcToModule'45'inv'45'p_314
      (coe
         MAlonzo.Code.Once.Parser.d_parseStrict_72
         (coe MAlonzo.Code.Once.Denotation.Behavior.d_srcText_52 (coe v0)))
