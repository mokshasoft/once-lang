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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.MainIRForm
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.SourceDenote
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.MainExtract.EffUU
d_EffUU_6 :: MAlonzo.Code.Once.Type.T_Type_112
d_EffUU_6
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_122)
-- Once.Adequacy.MainExtract.runMainˢ
d_runMain'738'_10 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_runMain'738'_10 ~v0 v1 v2 = du_runMain'738'_10 v1 v2
du_runMain'738'_10 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
du_runMain'738'_10 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_take_530 (coe v1)
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
            (coe
               MAlonzo.Code.Once.Denotation.SourceDenote.du_'10214'_'10215''738'_98
               (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe d_EffUU_6)
               (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
            (coe (\ v2 -> coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
         (coe v1))
-- Once.Adequacy.MainExtract.bind-cong-trace
d_bind'45'cong'45'trace_30 ::
  () ->
  () ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind'45'cong'45'trace_30 = erased
-- Once.Adequacy.MainExtract.source-meaningᴰ
d_source'45'meaning'7472'_54 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_source'45'meaning'7472'_54 v0 ~v1 ~v2
  = du_source'45'meaning'7472'_54 v0
du_source'45'meaning'7472'_54 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_source'45'meaning'7472'_54 v0
  = let v1
          = MAlonzo.Code.Once.Parser.d_guardDistinct_476
              (coe
                 MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_190
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                 (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
           -> let v3 = erased in
              coe
                (case coe v3 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v3))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> let v5
                           = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_336
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v4))
                               (coe
                                  MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                                  (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
                               (coe v3) (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                            -> let v7 = erased in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v10) (coe v7))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.Adequacy.MainIRForm.du_caf'45'go'45'find'45'form_364
                                         (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v4))
                                         (coe
                                            MAlonzo.Code.Once.Compile.d_collectSigEffects_462
                                            (coe
                                               MAlonzo.Code.Once.Parser.Module.Core.d_decls_48
                                               (coe v0)))
                                         (coe v3)
                                         (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v10) erased)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.MainExtract._.bridge
d_bridge_84 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_84 = erased
