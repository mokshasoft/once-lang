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

module MAlonzo.Code.Once.Adequacy.MainExtract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Adequacy.MainForm
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.MainExtract.EffUU
d_EffUU_16 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112
d_EffUU_16 ~v0 = du_EffUU_16
du_EffUU_16 :: MAlonzo.Code.Once.Type.T_Type_112
du_EffUU_16
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
-- Once.Adequacy.MainExtract.runMainˢ
d_runMain'738'_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_runMain'738'_20 v0 ~v1 v2 v3 = du_runMain'738'_20 v0 v2 v3
du_runMain'738'_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
du_runMain'738'_20 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v2)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
            (coe
               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_114
               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
               (coe du_EffUU_16) (coe v1) (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe (\ v3 -> coe v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
         (coe v2))
-- Once.Adequacy.MainExtract.bind-cong-trace
d_bind'45'cong'45'trace_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind'45'cong'45'trace_40 = erased
-- Once.Adequacy.MainExtract._.Form
d_Form_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> ()
d_Form_56 = erased
-- Once.Adequacy.MainExtract.source-meaningᴰ-aux
d_source'45'meaning'7472''45'aux_68 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_source'45'meaning'7472''45'aux_68 ~v0 ~v1 v2
  = du_source'45'meaning'7472''45'aux_68 v2
du_source'45'meaning'7472''45'aux_68 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_source'45'meaning'7472''45'aux_68 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainExtract._.bridge
d_bridge_84 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_84 = erased
-- Once.Adequacy.MainExtract.source-meaningᴰ
d_source'45'meaning'7472'_102 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_source'45'meaning'7472'_102 ~v0 v1 ~v2 ~v3
  = du_source'45'meaning'7472'_102 v1
du_source'45'meaning'7472'_102 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_source'45'meaning'7472'_102 v0
  = coe
      du_source'45'meaning'7472''45'aux_68
      (coe
         MAlonzo.Code.Once.Adequacy.MainForm.du_main'45'ir'45'form_256
         (coe v0))
