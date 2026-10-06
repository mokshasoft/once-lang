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

module MAlonzo.Code.Once.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit
import qualified MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.CCC.Codegen.NodesOK
import qualified MAlonzo.Code.Once.CCC.Codegen.ProgramImage
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV
import qualified MAlonzo.Code.Once.CCC.Target.RiscV64.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Principal
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Compile._._∈_
d__'8712'__6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d__'8712'__6 = erased
-- Once.Compile._._∈?_
d__'8712''63'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__8
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Compile.validateMain
d_validateMain_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain_10 v0
  = let v1
          = coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
              (coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                 ("main must have type IO Unit (= Eff Unit Unit), but got: "
                  ::
                  Data.Text.Text)
                 (MAlonzo.Code.Once.Type.d_showType_210 (coe v0))) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C_Unit_120
                  -> case coe v3 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v6 of
                                     MAlonzo.Code.Once.Type.C_eff_36
                                       -> case coe v4 of
                                            MAlonzo.Code.Once.Type.C_Unit_120
                                              -> coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> coe v1
                                     _ -> coe v1
                              _ -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v1
         _ -> coe v1)
-- Once.Compile.directCallIR
d_directCallIR_20 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_directCallIR_20 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Once.Type.C_Unit_120)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Zero_6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Type.C_Unit_120)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)))
                                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                             (coe MAlonzo.Code.Once.Type.C_Unit_120))
                                          v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       MAlonzo.Code.Once.Type.C_One_8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)))
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                             (coe MAlonzo.Code.Once.Type.C_Unit_120))
                                          v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
                                          (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v5)))
                                       (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3)))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                             (coe MAlonzo.Code.Once.Type.C_Unit_120))
                                          v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.Compile.FunCtx
d_FunCtx_50 :: ()
d_FunCtx_50 = erased
-- Once.Compile.emptyFunCtx
d_emptyFunCtx_52 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyFunCtx_52 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.extendFunCtx
d_extendFunCtx_54 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_54 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody-aux
d_compileFunBody'45'aux_70 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody'45'aux_70 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_compileFunBody'45'aux_70 v0 v1 v3 v4 v5 v6 v7 v8 v10
du_compileFunBody'45'aux_70 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody'45'aux_70 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Optimize.d_optimize_1238
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v0))))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_996
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v0))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v0))
                             (coe v11) (coe v7)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                                (coe v7) (coe v4) (coe v5)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420 (coe v3)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0)
                                   (coe v1) (coe v7) (coe v11) (coe v10)))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_996
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v0))
                          (coe v11) (coe v7)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                             (coe v7) (coe v4) (coe v5)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420 (coe v3)))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0) (coe v1)
                                (coe v7) (coe v11) (coe v10)))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v11
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("Type error in " :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v6
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (": " :: Data.Text.Text)
                             (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_92 (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBody
d_compileFunBody_120 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_120 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFunBody_120 v1 v2 v3 v4 v5 v6 v7
du_compileFunBody_120 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody_120 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFunBody'45'aux_70
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420 (coe v1))
         (coe v2)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418 (coe v1)))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
            (coe v1) (coe v2))
         (coe v6) (coe v5))
-- Once.Compile.compileFun-main-aux
d_compileFun'45'main'45'aux_142 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'main'45'aux_142 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'main'45'aux_142 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'main'45'aux_142 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'main'45'aux_142 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             du_compileFunBody_120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFun-aux
d_compileFun'45'aux_182 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'aux_182 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'aux_182 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'aux_182 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'aux_182 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_compileFun'45'main'45'aux_142 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_validateMain_10 (coe v5))
      else coe
             du_compileFunBody_120 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Compile.compileFun
d_compileFun_220 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_220 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFun_220 v1 v2 v3 v4 v5 v6 v7
du_compileFun_220 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun_220 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFun'45'aux_182 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.CompiledFun
d_CompiledFun_238 = ()
data T_CompiledFun_238
  = C_mkCompiledFun_252 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                        MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.IR.T_IR_16
-- Once.Compile.CompiledFun.cfName
d_cfName_246 ::
  T_CompiledFun_238 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_cfName_246 v0
  = case coe v0 of
      C_mkCompiledFun_252 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_248 ::
  T_CompiledFun_238 -> MAlonzo.Code.Once.Type.T_Type_108
d_cfType_248 v0
  = case coe v0 of
      C_mkCompiledFun_252 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_250 :: T_CompiledFun_238 -> MAlonzo.Code.Once.IR.T_IR_16
d_cfIR_250 v0
  = case coe v0 of
      C_mkCompiledFun_252 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_254 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_254 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_52
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_108 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       d_extendFunCtx_54 (coe d_buildFunCtx_254 (coe v2))
                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe d_buildFunCtx_254 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_274 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_274 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyPolyCtx_20
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v1))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))))
             (coe d_buildPolyCtx_274 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType-validate
d_inferType'45'validate_280 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType'45'validate_280 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6228
                        (coe v0) (coe v1) (coe v4)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v6 v7 v8 v9
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v6
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType
d_inferType_316 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType_316 v0 v1 v2
  = let v3
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6212
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                    (coe v0) (coe v1))
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v4 v5 v6 v7 v8
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v4
           -> coe
                d_inferType'45'validate_280
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                   (coe v0) (coe v1))
                (coe v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Cannot infer type: " :: Data.Text.Text)
                   (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_92 (coe v4)))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Principal.d_principalGround_2134
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                      (coe v0) (coe v1))
                   (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.resolveFunType
d_resolveFunType_344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveFunType_344 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_inferType_316 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_360 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_360
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_72
-- Once.Compile.seqCheck
d_seqCheck_362 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_seqCheck_362 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.checkOK
d_checkOK_374 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_checkOK_374 ~v0 ~v1 ~v2 v3 = du_checkOK_374 v3
du_checkOK_374 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_checkOK_374 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.TypeCheck.Error.d_renderError_92 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope
d_CScope_378 = ()
data T_CScope_378
  = C_cscope_392 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Compile.CScope.csig
d_csig_386 ::
  T_CScope_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_csig_386 v0
  = case coe v0 of
      C_cscope_392 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope.cimps
d_cimps_388 ::
  T_CScope_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cimps_388 v0
  = case coe v0 of
      C_cscope_392 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope.ctele
d_ctele_390 ::
  T_CScope_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ctele_390 v0
  = case coe v0 of
      C_cscope_392 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emptyCScope
d_emptyCScope_394 :: T_CScope_378
d_emptyCScope_394
  = coe
      C_cscope_392 (coe d_emptyFunCtx_52) (coe d_emptyFunCtx_52)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.ctop
d_ctop_396 ::
  T_CScope_378 -> MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412
d_ctop_396 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_422
      (coe d_csig_386 (coe v0)) (coe d_cimps_388 (coe v0))
-- Once.Compile.telePolys
d_telePolys_400 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116]
d_telePolys_400
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
-- Once.Compile.cpolys
d_cpolys_402 ::
  T_CScope_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cpolys_402 v0
  = coe
      d_buildPolyCtx_274 (coe d_telePolys_400 (d_ctele_390 (coe v0)))
-- Once.Compile.declImps
d_declImps_406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412
d_declImps_406 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyTopCtx_424
      (:) v2 v3
        -> coe
             d_declImps'45'aux_412 (coe v2) (coe v3) (coe v1)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe
                   MAlonzo.Code.Once.Parser.d_pfunName_124
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.declImps-aux
d_declImps'45'aux_412 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412
d_declImps'45'aux_412 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))
             else coe seq (coe v5) (coe d_declImps_406 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.extendScope
d_extendScope_434 ::
  T_CScope_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CScope_378
d_extendScope_434 v0 v1 v2
  = coe
      C_cscope_392 (coe d_csig_386 (coe v0))
      (coe
         d_extendFunCtx_54 (coe d_cimps_388 (coe v0)) (coe v1) (coe v2))
      (coe d_ctele_390 (coe v0))
-- Once.Compile.extendSig
d_extendSig_442 ::
  T_CScope_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CScope_378
d_extendSig_442 v0 v1 v2
  = coe
      C_cscope_392
      (coe d_extendFunCtx_54 (coe d_csig_386 (coe v0)) (coe v1) (coe v2))
      (coe d_cimps_388 (coe v0)) (coe d_ctele_390 (coe v0))
-- Once.Compile.addEntry
d_addEntry_450 ::
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 -> T_CScope_378
d_addEntry_450 v0 v1
  = coe
      C_cscope_392 (coe d_csig_386 (coe v0)) (coe d_cimps_388 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
            (coe d_ctop_396 (coe v0)))
         (coe d_ctele_390 (coe v0)))
-- Once.Compile.consCF
d_consCF_456 ::
  T_CompiledFun_238 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consCF_456 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileEntries
d_compileEntries_466 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileEntries_466 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    d_ce'45'fun_470 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    d_ce'45'poly_500 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe
                       du_checkOK_374
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                             (coe d_ctop_396 (coe v2)) (coe d_cpolys_402 (coe v2)))
                          (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v6))
                          (coe
                             MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v6)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-fun
d_ce'45'fun_470 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'fun_470 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             d_ce'45'prim_474 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
      else coe
             d_ce'45'mono_484 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                d_resolveFunType_344 (coe d_ctop_396 (coe v2))
                (coe d_cpolys_402 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3)))
-- Once.Compile.ce-prim
d_ce'45'prim_474 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim_474 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_ce'45'prim'45'conc_480 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v6))
             (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_86 (coe v6))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("FFI signature without a type: " :: Data.Text.Text)
                (MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-prim-conc
d_ce'45'prim'45'conc_480 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim'45'conc_480 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                      -> coe
                           d_compileEntries_466 (coe v0) (coe v1)
                           (coe
                              d_extendSig_442 (coe v2)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v5))
                           (coe v4)
                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("FFI signature `" :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    ("` is not ground: " :: Data.Text.Text)
                                    (MAlonzo.Code.Once.Type.d_showType_210 (coe v5)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("FFI signature `" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("` hides an effect: " :: Data.Text.Text)
                             (MAlonzo.Code.Once.Type.d_showType_210 (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("FFI signature `" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is not concrete: " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showType_210 (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono
d_ce'45'mono_484 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono_484 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v5
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_ce'45'mono'45'g_490 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono-g
d_ce'45'mono'45'g_490 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'g_490 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             d_ce'45'mono'45'ir_496 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                du_compileFun_220 (coe v1) (coe d_ctop_396 (coe v2))
                (coe d_cpolys_402 (coe v2))
                (coe d_declImps_406 (coe d_ctele_390 (coe v2)))
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v5)
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("The type of `" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_funName_106 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` mentions a type parameter: " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showType_210 (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono-ir
d_ce'45'mono'45'ir_496 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'ir_496 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v6
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             d_consCF_456
             (coe
                C_mkCompiledFun_252
                (coe
                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)))
                (coe v5) (coe v7))
             (coe
                d_compileEntries_466 (coe v0) (coe v1)
                (coe
                   d_extendScope_434 (coe v2)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v5))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-poly
d_ce'45'poly_500 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'poly_500 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text) v6)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_compileEntries_466 (coe v0) (coe v1)
             (coe d_addEntry_450 (coe v2) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule-aux
d_compileResolvedModule'45'aux_718 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule'45'aux_718 v0 v1 ~v2 v3
  = du_compileResolvedModule'45'aux_718 v0 v1 v3
du_compileResolvedModule'45'aux_718 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileResolvedModule'45'aux_718 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             d_compileEntries_466 (coe v0) (coe v1) (coe d_emptyCScope_394)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_736 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_736 v0 v1 v2
  = coe
      du_compileResolvedModule'45'aux_718 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v2))
         (coe v2))
-- Once.Compile.compileModule
d_compileModule_744 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_744 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.d_r_370
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1038 (coe v2)))) in
    coe
      (let v4
             = MAlonzo.Code.Once.Parser.d_extractFunctions_572
                 (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v3))
                 (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
              -> coe
                   d_compileEntries_466 (coe v0) (coe v1) (coe d_emptyCScope_394)
                   (coe v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.emittedSyms
d_emittedSyms_778 ::
  [T_CompiledFun_238] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms_778 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                (coe d_cfName_246 (coe v1)))
             (coe d_emittedSyms_778 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms-aux
d_moduleSyms'45'aux_784 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms'45'aux_784 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_emittedSyms_778 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms
d_moduleSyms_788 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms_788 v0 v1 v2
  = coe
      d_moduleSyms'45'aux_784
      (coe d_compileResolvedModule_736 (coe v0) (coe v1) (coe v2))
-- Once.Compile.EffUU
d_EffUU_796 :: MAlonzo.Code.Once.Type.T_Type_108
d_EffUU_796
  = coe
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
      (coe
         MAlonzo.Code.Once.Type.C_mk'45'kind_50
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe MAlonzo.Code.Once.Type.C_eff_36))
      (coe MAlonzo.Code.Once.Type.C_Unit_120)
-- Once.Compile.isEffUU?
d_isEffUU'63'_800 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_isEffUU'63'_800 v0
  = let v1
          = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__192
              (coe v0) (coe d_EffUU_796) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                         -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.mainCall
d_mainCall_814 :: MAlonzo.Code.Once.IR.T_IR_16
d_mainCall_814
  = coe
      MAlonzo.Code.Once.IR.C_Call_138
      (MAlonzo.Code.Once.CanonicalName.d_bare_12
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.findMain-here
d_findMain'45'here_818 ::
  T_CompiledFun_238 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain'45'here_818 ~v0 v1 v2 v3
  = du_findMain'45'here_818 v1 v2 v3
du_findMain'45'here_818 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
du_findMain'45'here_818 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe d_mainCall_814)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.findMain
d_findMain_832 ::
  [T_CompiledFun_238] -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain_832 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             du_findMain'45'here_818
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__116
                (coe d_cfName_246 (coe v1))
                (coe
                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe ("main" :: Data.Text.Text))))
             (coe d_isEffUU'63'_800 (coe d_cfType_248 (coe v1)))
             (coe d_findMain_832 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToIR-aux
d_moduleToIR'45'aux_838 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR'45'aux_838 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_832 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToIR
d_moduleToIR_842 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR_842 v0
  = coe
      d_moduleToIR'45'aux_838
      (coe
         d_compileResolvedModule_736 (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Compile.irFunOf
d_irFunOf_846 ::
  T_CompiledFun_238 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_irFunOf_846 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe d_cfName_246 (coe v0))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_dc_854 (coe v0))))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_dc_854 (coe v0)))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_dc_854 (coe v0))))
-- Once.Compile._.dc
d_dc_854 ::
  T_CompiledFun_238 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dc_854 v0
  = coe
      d_directCallIR_20 (coe d_cfType_248 (coe v0))
      (coe d_cfIR_250 (coe v0))
-- Once.Compile.tableOf-go
d_tableOf'45'go_856 ::
  [T_CompiledFun_238] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf'45'go_856 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_tableOf'45'go_856 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_irFunOf_846 (coe v2)) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.tableOf
d_tableOf_866 ::
  [T_CompiledFun_238] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf_866 v0
  = coe
      d_tableOf'45'go_856 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.tableOfResult
d_tableOfResult_870 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOfResult_870 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_tableOf_866 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleTable
d_moduleTable_874 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_moduleTable_874 v0
  = coe
      d_tableOfResult_870
      (coe
         d_compileResolvedModule_736 (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Compile.programAt
d_programAt_878 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_programAt_878 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v0)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToProgram
d_moduleToProgram_886 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_moduleToProgram_886 v0
  = coe
      d_programAt_878 (coe d_moduleTable_874 (coe v0))
      (coe d_moduleToIR_842 (coe v0))
-- Once.Compile.rewrite-fun
d_rewrite'45'fun_890 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_rewrite'45'fun_890 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
            (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v0))))
-- Once.Compile.rewrite-table
d_rewrite'45'table_894 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_rewrite'45'table_894 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_rewrite'45'fun_890 (coe v1))
             (coe d_rewrite'45'table_894 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.rewrite-program
d_rewrite'45'program_900 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_rewrite'45'program_900 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
      (coe
         d_rewrite'45'table_894
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0))))
-- Once.Compile.program-blocks
d_program'45'blocks_904 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_program'45'blocks_904 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0))))
      (coe
         du_table'45'blocks_912
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0)))
-- Once.Compile._.table-blocks
d_table'45'blocks_912 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_table'45'blocks_912 ~v0 v1 = du_table'45'blocks_912 v1
du_table'45'blocks_912 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
du_table'45'blocks_912 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                   (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))))
             (coe du_table'45'blocks_912 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.dedup-go
d_dedup'45'go_918 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'go_918 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Data.Bool.ListAction.du_any_14
                       (coe
                          (\ v6 ->
                             MAlonzo.Code.Data.String.Properties.d__'61''61'__86
                               (coe v6) (coe v4)))
                       (coe v0))
                    (coe d_dedup'45'go_918 (coe v0) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe
                          d_dedup'45'go_918
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.dedup-blocks
d_dedup'45'blocks_932 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'blocks_932
  = coe
      d_dedup'45'go_918
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.block-symbol
d_block'45'symbol_934 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'symbol_934 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_366
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v0)))
-- Once.Compile.block-syms
d_block'45'syms_938 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_block'45'syms_938 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe
         d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_block'45'symbol_934 (coe v1)) (coe v1)))
            (coe v0)))
-- Once.Compile.calls-of
d_calls'45'of_944 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_calls'45'of_944 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_388 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_96
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))))
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_386 (coe v0)))
-- Once.Compile.is-extern?
d_is'45'extern'63'_954 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_is'45'extern'63'_954 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
         (coe v1)
         (coe d_block'45'syms_938 (coe d_program'45'blocks_904 (coe v0))))
-- Once.Compile.externs-of
d_externs'45'of_960 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_externs'45'of_960 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_filter_648
      (coe d_is'45'extern'63'_954 (coe v0))
      (coe d_calls'45'of_944 (coe d_rewrite'45'program_900 (coe v0)))
-- Once.Compile.entry-owner
d_entry'45'owner_964 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_entry'45'owner_964
  = coe
      MAlonzo.Code.Once.CanonicalName.d_bare_12
      (coe ("0entry" :: Data.Text.Text))
-- Once.Compile.FileOf
d_FileOf_966 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> ()
d_FileOf_966 = erased
-- Once.Compile.printFile
d_printFile_970 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printFile_970 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_print_84
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.image-of
d_image'45'of_972 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_image'45'of_972 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_42
      (coe d_entry'45'owner_964) (coe d_rewrite'45'program_900 (coe v0))
-- Once.Compile.blocks-x86-64
d_blocks'45'x86'45'64_976 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'x86'45'64_976 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
              (coe
                 MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_block'45'payload_192
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))))
      (coe
         d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'block'45'symbol_224
                       (coe v1))
                    (coe v1)))
            (coe d_program'45'blocks_904 (coe v0))))
-- Once.Compile.emit-x86-64
d_emit'45'x86'45'64_984 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
d_emit'45'x86'45'64_984 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_72
            (coe d_entry'45'owner_964) (coe (0 :: Integer))
            (coe d_image'45'of_972 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'x86'45'64_976 (coe v0))
      (coe d_externs'45'of_960 (coe v0))
-- Once.Compile.blocks-x86-32
d_blocks'45'x86'45'32_988 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'x86'45'32_988 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
              (coe
                 MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_block'45'payload_192
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))))
      (coe
         d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'block'45'symbol_224
                       (coe v1))
                    (coe v1)))
            (coe d_program'45'blocks_904 (coe v0))))
-- Once.Compile.emit-x86-32
d_emit'45'x86'45'32_996 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
d_emit'45'x86'45'32_996 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace'45'cnt_232
            (coe d_entry'45'owner_964) (coe (0 :: Integer))
            (coe d_image'45'of_972 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'x86'45'32_988 (coe v0))
      (coe d_externs'45'of_960 (coe v0))
-- Once.Compile.blocks-riscv64
d_blocks'45'riscv64_1000 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'riscv64_1000 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
              (coe
                 MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_block'45'payload_210
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))))
      (coe
         d_dedup'45'blocks_932
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_arith'45'block'45'symbol_242
                       (coe v1))
                    (coe v1)))
            (coe d_program'45'blocks_904 (coe v0))))
-- Once.Compile.emit-riscv64
d_emit'45'riscv64_1008 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
d_emit'45'riscv64_1008 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace'45'cnt_262
            (coe d_entry'45'owner_964) (coe (0 :: Integer))
            (coe d_image'45'of_972 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'riscv64_1000 (coe v0))
      (coe d_externs'45'of_960 (coe v0))
-- Once.Compile.emitProgram
d_emitProgram_1014 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 -> AgdaAny
d_emitProgram_1014 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe d_emit'45'x86'45'64_984
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe d_emit'45'x86'45'32_996
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe d_emit'45'riscv64_1008
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lib-image
d_lib'45'image_1016 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250]
d_lib'45'image_1016 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
      (coe (0 :: Integer)) (coe d_rewrite'45'table_894 (coe v0))
-- Once.Compile.lib-program
d_lib'45'program_1020 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380
d_lib'45'program_1020 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_390 (coe v0)
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.Compile.lib-blocks
d_lib'45'blocks_1024 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_lib'45'blocks_1024 v0
  = coe d_program'45'blocks_904 (coe d_lib'45'program_1020 (coe v0))
-- Once.Compile.emitLibrary
d_emitLibrary_1030 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> AgdaAny
d_emitLibrary_1030 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_72
                   (coe d_entry'45'owner_964) (coe (0 :: Integer))
                   (coe d_lib'45'image_1016 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_block'45'payload_192
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
                (coe
                   d_dedup'45'blocks_932
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86Z45Z64.Emit.d_arith'45'block'45'symbol_224
                                 (coe v2))
                              (coe v2)))
                      (coe d_lib'45'blocks_1024 (coe v1)))))
             (coe d_externs'45'of_960 (coe d_lib'45'program_1020 (coe v1)))
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace'45'cnt_232
                   (coe d_entry'45'owner_964) (coe (0 :: Integer))
                   (coe d_lib'45'image_1016 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_block'45'payload_192
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
                (coe
                   d_dedup'45'blocks_932
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.X86Z45Z32.Emit.d_arith'45'block'45'symbol_224
                                 (coe v2))
                              (coe v2)))
                      (coe d_lib'45'blocks_1024 (coe v1)))))
             (coe d_externs'45'of_960 (coe d_lib'45'program_1020 (coe v1)))
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe
             MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace'45'cnt_262
                   (coe d_entry'45'owner_964) (coe (0 :: Integer))
                   (coe d_lib'45'image_1016 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                        (coe
                           MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_block'45'payload_210
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
                (coe
                   d_dedup'45'blocks_932
                   (coe
                      MAlonzo.Code.Data.List.Base.du_map_22
                      (coe
                         (\ v2 ->
                            coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.Arith.Backend.RiscV64.Emit.d_arith'45'block'45'symbol_242
                                 (coe v2))
                              (coe v2)))
                      (coe d_lib'45'blocks_1024 (coe v1)))))
             (coe d_externs'45'of_960 (coe d_lib'45'program_1020 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emit-at
d_emit'45'at_1052 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [T_CompiledFun_238] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_emit'45'at_1052 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             d_emitProgram_1014 v0
             (coe
                MAlonzo.Code.Once.Denotation.Program.C_irProgram_390
                (coe d_tableOf_866 (coe v1)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_emitLibrary_1030 (coe v0) (coe d_tableOf_866 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emitFromCompiled
d_emitFromCompiled_1066 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_emitFromCompiled_1066 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                d_emit'45'at_1052 (coe v0) (coe v2) (coe d_findMain_832 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Stage
d_Stage_1076 = ()
data T_Stage_1076 = C_Parse_1078 | C_Check_1080 | C_Build_1082
-- Once.Compile.CompileResult
d_CompileResult_1084 = ()
data T_CompileResult_1084
  = C_Parsed_1086 [MAlonzo.Code.Once.Parser.T_FunInfo_96]
                  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] |
    C_Checked_1088 [T_CompiledFun_238] |
    C_Built_1090 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_1092 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.built-of
d_built'45'of_1096 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1084
d_built'45'of_1096 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_Error_1092 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe C_Built_1090 (coe d_printFile_970 v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showFunInfo
d_showFunInfo_1106 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_1106 v0
  = let v1 = MAlonzo.Code.Once.Parser.d_funType_108 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_106 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" : " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_210 (coe v2)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_106 (coe v0))
                (" : <inferred>" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_1120 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_1120 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_440
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_1124 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_1124 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_1106 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_1124 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_1106 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_1132 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_1132 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_1120 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_1132 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_1120 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_1140 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1076 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_1084
d_compile_1140 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                          (coe (0 :: Integer)))
                       (coe
                          MAlonzo.Code.Once.Parser.Core.d_skipNewlines_282
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                             (coe (0 :: Integer))))
                       (\ v5 v6 v7 ->
                          coe
                            MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                               (coe (0 :: Integer)))))))
              (coe
                 MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Parser.Module.d_r_370
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                          (coe (0 :: Integer))))))
              (coe
                 MAlonzo.Code.Once.Parser.d_allTrailing_18
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                             (coe (0 :: Integer)))
                          (coe
                             MAlonzo.Code.Once.Parser.Core.d_skipNewlines_282
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                                (coe (0 :: Integer))))
                          (\ v5 v6 v7 ->
                             coe
                               MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_640
                                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                                  (coe (0 :: Integer)))))))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe C_Error_1092 (coe v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = MAlonzo.Code.Once.Parser.d_extractFunctions_572
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v6))
                        (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe C_Error_1092 (coe v8)
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> case coe v1 of
                          C_Parse_1078
                            -> coe
                                 C_Parsed_1086 (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v8))
                                 (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v8))
                          C_Check_1080
                            -> let v9
                                     = d_compileEntries_466
                                         (coe v0) (coe v2) (coe d_emptyCScope_394) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1092 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe C_Checked_1088 (coe v10)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_Build_1082
                            -> let v9
                                     = d_compileEntries_466
                                         (coe v0) (coe v2) (coe d_emptyCScope_394) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1092 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe
                                           d_built'45'of_1096 (coe v3)
                                           (coe d_emitFromCompiled_1066 (coe v3) (coe v9))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.cfm-check-emit
d_cfm'45'check'45'emit_1202 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1084
d_cfm'45'check'45'emit_1202 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_Error_1092 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe C_Checked_1088 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.litRangeError
d_litRangeError_1208 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_litRangeError_1208 v0 v1
  = coe
      du_badLit_1220 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Admissible.d_firstBadLit_106 (coe v0)
         (coe v1))
-- Once.Compile._.bits
d_bits_1218 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> Integer
d_bits_1218 v0 ~v1 = du_bits_1218 v0
du_bits_1218 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> Integer
du_bits_1218 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_80 (coe v0)
-- Once.Compile._.badLit
d_badLit_1220 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_badLit_1220 v0 ~v1 v2 = du_badLit_1220 v0 v2
du_badLit_1220 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_badLit_1220 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Int literal " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" does not fit " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.Target.Arch.d_archName_88 (coe v0))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("'s signed " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe
                               MAlonzo.Code.Data.Nat.Show.d_show_56 (coe du_bits_1218 (coe v0)))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("-bit range (-2^" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe
                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                        (coe du_bits_1218 (coe v0)) (1 :: Integer)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (" .. 2^" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (coe
                                           MAlonzo.Code.Data.Nat.Show.d_show_56
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                              (coe du_bits_1218 (coe v0)) (1 :: Integer)))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           ("-1). " :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              ("Once's Int is the TARGET's word (D054), so this literal is "
                                               ::
                                               Data.Text.Text)
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 ("expressible on a wider target and not on this one. Arithmetic "
                                                  ::
                                                  Data.Text.Text)
                                                 ("wraps; a literal does not."
                                                  ::
                                                  Data.Text.Text)))))))))))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Int literal out of range for " :: Data.Text.Text)
             (MAlonzo.Code.Once.Target.Arch.d_archName_88 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-file-gated
d_cfm'45'file'45'gated_1228 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cfm'45'file'45'gated_1228 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       d_emitFromCompiled_1066 (coe v2)
                       (coe
                          d_compileEntries_466 (coe v0) (coe v1) (coe d_emptyCScope_394)
                          (coe v4)))
             else coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe d_litRangeError_1208 (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-file-ef
d_cfm'45'file'45'ef_1252 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cfm'45'file'45'ef_1252 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             d_cfm'45'file'45'gated_1228 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFileFromModule
d_compileFileFromModule_1276 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFileFromModule_1276 v0 v1 v2 v3
  = coe
      d_cfm'45'file'45'ef_1252 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v3))
         (coe v3))
-- Once.Compile.cfm-stage-aux
d_cfm'45'stage'45'aux_1286 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1076 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_CompileResult_1084
d_cfm'45'stage'45'aux_1286 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      C_Parse_1078
        -> coe
             C_Parsed_1086 (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v5))
             (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v5))
      C_Check_1080
        -> coe
             d_cfm'45'check'45'emit_1202
             (coe
                d_compileEntries_466 (coe v0) (coe v2) (coe d_emptyCScope_394)
                (coe v5))
      C_Build_1082
        -> coe
             d_built'45'of_1096 (coe v3)
             (coe
                d_cfm'45'file'45'gated_1228 (coe v0) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                   (coe v3) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-ef-aux
d_cfm'45'ef'45'aux_1318 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1076 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1084
d_cfm'45'ef'45'aux_1318 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe C_Error_1092 (coe v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_cfm'45'stage'45'aux_1286 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFromModule
d_compileFromModule_1344 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1076 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_CompileResult_1084
d_compileFromModule_1344 v0 v1 v2 v3 v4
  = coe
      d_cfm'45'ef'45'aux_1318 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v4))
         (coe v4))
