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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Principal
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.Honest
import qualified MAlonzo.Code.Once.Internal.Type.Instance
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.LoopWarn
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolFresh
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
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
-- Once.Compile.mainType
d_mainType_12 :: Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_mainType_12 ~v0 = du_mainType_12
du_mainType_12 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_mainType_12
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
-- Once.Compile.validateMain-at
d_validateMain'45'at_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain'45'at_18 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("main must be usable as Eff Unit Unit (its type below it), but its type is "
                           ::
                           Data.Text.Text)
                          (MAlonzo.Code.Once.Type.d_showType_36 (coe v0) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.validateMain
d_validateMain_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain_26 v0 v1
  = coe
      d_validateMain'45'at_18 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170 (coe v0) (coe v1)
         (coe du_mainType_12))
-- Once.Compile.firstChecking
d_firstChecking_36 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_firstChecking_36 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v4 v5
        -> coe
             d_fc'45'step_46 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6500 (coe v0)
                (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.fc-step
d_fc'45'step_46 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Once.Spec.Type.T_Ty_8] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_fc'45'step_46 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v8 v9 v10 v11
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v8
               -> coe d_firstChecking_36 (coe v0) (coe v1) (coe v2) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.directCallIR
d_directCallIR_84 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_directCallIR_84 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                             (coe v6)))
                                       (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                             (coe (0 :: Integer))
                                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                          v2 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       MAlonzo.Code.Once.Spec.Grade.C_One_10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                             (coe v4))
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                             (coe v6)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                          (coe v4)))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                             (coe (0 :: Integer))
                                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                          v2 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IR.C__'8728'__28
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20
                                       (coe
                                          MAlonzo.Code.Once.IRTy.C__'8667'__24
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                             (coe v4))
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                             (coe v6)))
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0)
                                          (coe v4)))
                                    (coe MAlonzo.Code.Once.IR.C_apply_90)
                                    (coe
                                       MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                                       (coe
                                          MAlonzo.Code.Once.IR.C__'8728'__28
                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                             (coe (0 :: Integer))
                                             (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                          v2 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                                       (coe MAlonzo.Code.Once.IR.C_id_20))))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.Compile.FunCtx
d_FunCtx_114 :: ()
d_FunCtx_114 = erased
-- Once.Compile.emptyFunCtx
d_emptyFunCtx_116 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyFunCtx_116
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.extendFunCtx
d_extendFunCtx_118 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_118 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody-aux
d_compileFunBody'45'aux_134 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody'45'aux_134 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_compileFunBody'45'aux_134 v0 v1 v3 v4 v5 v6 v7 v8 v10
du_compileFunBody'45'aux_134 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody'45'aux_134 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Optimize.d_optimize_1254
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.Internal.Context.du_'10214'_'10215''7580'_26
                                (coe
                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136
                                   (coe v0))))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                             (coe (0 :: Integer)) (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1046
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v0))
                             (coe v11) (coe v7)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4170
                                (coe (0 :: Integer)) (coe v7) (coe v4) (coe v5)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v3)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize_22
                                   (coe (0 :: Integer)) (coe v0) (coe v1) (coe v7) (coe v11)
                                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1046
                          (coe (0 :: Integer))
                          (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
                          (coe
                             MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v0))
                          (coe v11) (coe v7)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4170
                             (coe (0 :: Integer)) (coe v7) (coe v4) (coe v5)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v3)))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.Denotation.Realize.d_realize_22
                                (coe (0 :: Integer)) (coe v0) (coe v1) (coe v7) (coe v11)
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v11
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
                             (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_96 (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBody
d_compileFunBody_184 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_184 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFunBody_184 v1 v2 v3 v4 v5 v6 v7
du_compileFunBody_184 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody_184 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFunBody'45'aux_134
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
         (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1))
         (coe v2)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1))
         (\ v7 -> coe MAlonzo.Code.Once.Spec.Type.du_'8709''8342'_142))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6500
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v1) (coe v2))
         (coe v6) (coe v5))
-- Once.Compile.compileFun-main-aux
d_compileFun'45'main'45'aux_206 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'main'45'aux_206 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'main'45'aux_206 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'main'45'aux_206 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'main'45'aux_206 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             du_compileFunBody_184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFun-aux
d_compileFun'45'aux_246 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'aux_246 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'aux_246 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'aux_246 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'aux_246 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_compileFun'45'main'45'aux_206 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_validateMain_26 (coe (0 :: Integer)) (coe v5))
      else coe
             du_compileFunBody_184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Compile.compileFun
d_compileFun_284 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_284 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFun_284 v1 v2 v3 v4 v5 v6 v7
du_compileFun_284 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun_284 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFun'45'aux_246 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.compileFunBodyI-at
d_compileFunBodyI'45'at_316 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBodyI'45'at_316 v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10
                            v11 ~v12 v13 v14
  = du_compileFunBodyI'45'at_316 v0 v1 v3 v6 v7 v8 v9 v10 v11 v13 v14
du_compileFunBodyI'45'at_316 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBodyI'45'at_316 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
        -> if coe v11
             then coe
                    seq (coe v12)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Optimize.d_optimize_1254
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Internal.Context.du_'10214'_'10215''7580'_26
                                   (coe
                                      MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136
                                      (coe v0))))
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50
                                (coe (0 :: Integer)) (coe v8))
                             (coe
                                MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1046
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
                                (coe
                                   MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v0))
                                (coe v2) (coe v8)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4170
                                   (coe (0 :: Integer)) (coe v8) (coe v5) (coe v6)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                         (coe v8))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v4)))
                                   (coe (0 :: Integer))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_34
                                      (coe (0 :: Integer)) (coe v0) (coe v1) (coe v8) (coe v2)
                                      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9))))))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1046
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Internal.Typing.Scope.d_size_132 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Internal.Typing.Scope.d_debruijn_136 (coe v0))
                             (coe v2) (coe v8)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4170
                                (coe (0 :: Integer)) (coe v8) (coe v5) (coe v6)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v8))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v4)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_34
                                   (coe (0 :: Integer)) (coe v0) (coe v1) (coe v8) (coe v2)
                                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))))))
             else coe
                    seq (coe v12)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Type error in " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v7
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (": its body synthesizes another type than " :: Data.Text.Text)
                                (MAlonzo.Code.Once.Type.d_showType_36
                                   (coe (0 :: Integer)) (coe v8))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBodyI-aux
d_compileFunBodyI'45'aux_370 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBodyI'45'aux_370 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_compileFunBodyI'45'aux_370 v0 v1 v3 v4 v5 v6 v7 v8 v10
du_compileFunBodyI'45'aux_370 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBodyI'45'aux_370 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v11 v12 v13 v14 v15
               -> coe
                    du_compileFunBodyI'45'at_316 (coe v0) (coe v1) (coe v12) (coe v2)
                    (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__230
                       (coe (0 :: Integer)) (coe v11) (coe v7))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_100 v11
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
                             (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_96 (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunBodyI
d_compileFunBodyI_414 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBodyI_414 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFunBodyI_414 v1 v2 v3 v4 v5 v6 v7
du_compileFunBodyI_414 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBodyI_414 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFunBodyI'45'aux_370
      (coe
         MAlonzo.Code.Once.Internal.Typing.Scope.C_mkCtx_146
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
         (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1))
         (coe v2)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1))
         (\ v7 -> coe MAlonzo.Code.Once.Spec.Type.du_'8709''8342'_142))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6490
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v1) (coe v2))
         (coe v6))
-- Once.Compile.compileFunI-main-aux
d_compileFunI'45'main'45'aux_436 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunI'45'main'45'aux_436 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFunI'45'main'45'aux_436 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFunI'45'main'45'aux_436 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunI'45'main'45'aux_436 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             du_compileFunBodyI_414 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunI-aux
d_compileFunI'45'aux_476 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunI'45'aux_476 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFunI'45'aux_476 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFunI'45'aux_476 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunI'45'aux_476 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_compileFunI'45'main'45'aux_436 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe d_validateMain_26 (coe (0 :: Integer)) (coe v5))
      else coe
             du_compileFunBodyI_414 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Compile.compileFunI
d_compileFunI_514 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunI_514 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFunI_514 v1 v2 v3 v4 v5 v6 v7
du_compileFunI_514 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunI_514 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFunI'45'aux_476 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.compileFunM
d_compileFunM_536 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunM_536 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 ->
                coe du_compileFun_284 v3 v4 v5 v6 v7 v8 v9)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 v3 v4 v5 v6 v7 v8 ->
                coe du_compileFunI_514 v2 v3 v4 v5 v6 v7 v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun
d_CompiledFun_538 = ()
data T_CompiledFun_538
  = C_mkCompiledFun_552 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                        MAlonzo.Code.Once.Spec.Type.T_Ty_8 MAlonzo.Code.Once.IR.T_IR_16
-- Once.Compile.CompiledFun.cfName
d_cfName_546 ::
  T_CompiledFun_538 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_cfName_546 v0
  = case coe v0 of
      C_mkCompiledFun_552 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_548 ::
  T_CompiledFun_538 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_cfType_548 v0
  = case coe v0 of
      C_mkCompiledFun_552 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_550 :: T_CompiledFun_538 -> MAlonzo.Code.Once.IR.T_IR_16
d_cfIR_550 v0
  = case coe v0 of
      C_mkCompiledFun_552 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_554 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_76] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_554 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_116
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_88 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       d_extendFunCtx_118 (coe d_buildFunCtx_554 (coe v2))
                       (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v1)) (coe v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe d_buildFunCtx_554 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_574 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_574 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyPolyCtx_8
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.d_pfunName_104 (coe v1))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v1))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_108 (coe v1))))
             (coe d_buildPolyCtx_574 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType
d_inferType_580 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType_580 v0 v1 v2
  = let v3
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6490
                 (coe (0 :: Integer))
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                    (coe v0) (coe v1))
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v4 v5 v6 v7 v8
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_100 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("The body has no type of its own (" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_96 (coe v4))
                      ("): a definition without a signature must synthesize its type; give it a signature"
                       ::
                       Data.Text.Text)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.resolveFunType
d_resolveFunType_608 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveFunType_608 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_inferType_580 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_624 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_624
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_72
-- Once.Compile.checkOK
d_checkOK_634 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_checkOK_634 ~v0 ~v1 ~v2 ~v3 v4 = du_checkOK_634 v4
du_checkOK_634 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_checkOK_634 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v3
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.TypeCheck.Error.d_renderError_96 (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope
d_CScope_638 = ()
data T_CScope_638
  = C_cscope_652 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Compile.CScope.csig
d_csig_646 ::
  T_CScope_638 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_csig_646 v0
  = case coe v0 of
      C_cscope_652 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope.cimps
d_cimps_648 ::
  T_CScope_638 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cimps_648 v0
  = case coe v0 of
      C_cscope_652 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope.ctele
d_ctele_650 ::
  T_CScope_638 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ctele_650 v0
  = case coe v0 of
      C_cscope_652 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emptyCScope
d_emptyCScope_654 :: T_CScope_638
d_emptyCScope_654
  = coe
      C_cscope_652 (coe d_emptyFunCtx_116) (coe d_emptyFunCtx_116)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.ctop
d_ctop_656 ::
  T_CScope_638 -> MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332
d_ctop_656 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.C_topCtx_342
      (coe d_csig_646 (coe v0)) (coe d_cimps_648 (coe v0))
-- Once.Compile.telePolys
d_telePolys_660 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_96]
d_telePolys_660
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
-- Once.Compile.cpolys
d_cpolys_662 ::
  T_CScope_638 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cpolys_662 v0
  = coe
      d_buildPolyCtx_574 (coe d_telePolys_660 (d_ctele_650 (coe v0)))
-- Once.Compile.declImps
d_declImps_666 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332
d_declImps_666 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptyTopCtx_344
      (:) v2 v3
        -> coe
             d_declImps'45'aux_672 (coe v2) (coe v3) (coe v1)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe
                   MAlonzo.Code.Once.Parser.d_pfunName_104
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.declImps-aux
d_declImps'45'aux_672 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332
d_declImps'45'aux_672 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))
             else coe seq (coe v5) (coe d_declImps_666 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.extendDefs
d_extendDefs_694 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendDefs_694 v0 v1 v2
  = coe
      d_extendDefs'45'at_696
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v1)
         (coe ("main" :: Data.Text.Text)))
      (coe v0) (coe v1) (coe v2)
-- Once.Compile.extendDefs-at
d_extendDefs'45'at_696 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendDefs'45'at_696 v0 v1 v2 v3
  = if coe v0
      then coe v1
      else coe d_extendFunCtx_118 (coe v1) (coe v2) (coe v3)
-- Once.Compile.extendScope
d_extendScope_716 ::
  T_CScope_638 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CScope_638
d_extendScope_716 v0 v1 v2
  = coe
      C_cscope_652 (coe d_csig_646 (coe v0))
      (coe d_extendDefs_694 (coe d_cimps_648 (coe v0)) (coe v1) (coe v2))
      (coe d_ctele_650 (coe v0))
-- Once.Compile.extendSig
d_extendSig_724 ::
  T_CScope_638 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_CScope_638
d_extendSig_724 v0 v1 v2
  = coe
      C_cscope_652
      (coe
         d_extendFunCtx_118 (coe d_csig_646 (coe v0)) (coe v1) (coe v2))
      (coe d_cimps_648 (coe v0)) (coe d_ctele_650 (coe v0))
-- Once.Compile.addEntry
d_addEntry_732 ::
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_96 -> T_CScope_638
d_addEntry_732 v0 v1
  = coe
      C_cscope_652 (coe d_csig_646 (coe v0)) (coe d_cimps_648 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
            (coe d_ctop_656 (coe v0)))
         (coe d_ctele_650 (coe v0)))
-- Once.Compile.consCF
d_consCF_738 ::
  T_CompiledFun_538 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consCF_738 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileEntries
d_compileEntries_748 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileEntries_748 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_114 v6
               -> coe
                    d_ce'45'fun_752 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_92 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_116 v6
               -> coe
                    d_ce'45'poly'45'p_782 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe
                       d_firstChecking_36
                       (coe
                          MAlonzo.Code.Once.Internal.Type.Instance.d_arityOf_88
                          (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v6)))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                          (coe
                             MAlonzo.Code.Once.Internal.Type.Instance.d_kindsOf_168
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v6)))
                          (coe d_ctop_656 (coe v2)) (coe d_cpolys_662 (coe v2)))
                       (coe MAlonzo.Code.Once.Parser.d_pfunBody_108 (coe v6))
                       (coe
                          MAlonzo.Code.Once.Internal.Principal.du_below_12
                          (coe
                             MAlonzo.Code.Once.Internal.Type.Instance.d_rigidOf_162
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v6)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-fun
d_ce'45'fun_752 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'fun_752 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             d_ce'45'prim_756 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Parser.d_funType_88 (coe v3))
      else coe
             d_ce'45'mono_766 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                d_resolveFunType_608 (coe d_ctop_656 (coe v2))
                (coe d_cpolys_662 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funType_88 (coe v3))
                (coe MAlonzo.Code.Once.Parser.d_funBody_90 (coe v3)))
-- Once.Compile.ce-prim
d_ce'45'prim_756 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim_756 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_ce'45'prim'45'conc_762 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v6))
             (coe
                MAlonzo.Code.Once.Internal.Type.Honest.d_honest'63'_202 (coe v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("FFI signature without a type: " :: Data.Text.Text)
                (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-prim-conc
d_ce'45'prim'45'conc_762 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsConcrete_30 ->
  Maybe AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim'45'conc_762 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    d_compileEntries_748 (coe v0) (coe v1)
                    (coe
                       d_extendSig_724 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v3)) (coe v5))
                    (coe v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("FFI signature `" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3))
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("` hides an effect: " :: Data.Text.Text)
                             (MAlonzo.Code.Once.Type.d_showType_36
                                (coe (0 :: Integer)) (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("FFI signature `" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is not concrete: " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showType_36
                         (coe (0 :: Integer)) (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono
d_ce'45'mono_766 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono_766 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v5
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_ce'45'mono'45'p_772 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe
                d_firstChecking_36 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                   (coe d_ctop_656 (coe v2)) (coe d_cpolys_662 (coe v2)))
                (coe MAlonzo.Code.Once.Parser.d_funBody_90 (coe v3))
                (coe MAlonzo.Code.Once.Internal.Principal.du_below_12 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono-p
d_ce'45'mono'45'p_772 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'p_772 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("`" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is more precise than its signature " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Once.Type.d_showType_36
                            (coe (0 :: Integer)) (coe v5))
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (": the body also checks at " :: Data.Text.Text)
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               (MAlonzo.Code.Once.Type.d_showType_36
                                  (coe (0 :: Integer)) (coe v7))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (". A signature states the body's own type: write the more precise one, or give the body"
                                   ::
                                   Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (" the wider type with an annotation, " :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3))
                                        (coe
                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                           (" = (... : " :: Data.Text.Text)
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (MAlonzo.Code.Once.Type.d_showType_36
                                                 (coe (0 :: Integer)) (coe v5))
                                              (")" :: Data.Text.Text))))))))))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_ce'45'mono'45'ir_778 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                d_compileFunM_536 (MAlonzo.Code.Once.Parser.d_funType_88 (coe v3))
                v0 v1 (d_ctop_656 (coe v2)) (d_cpolys_662 (coe v2))
                (d_declImps_666 (coe d_ctele_650 (coe v2)))
                (MAlonzo.Code.Once.Parser.d_funName_86 (coe v3)) v5
                (MAlonzo.Code.Once.Parser.d_funBody_90 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono-ir
d_ce'45'mono'45'ir_778 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'ir_778 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v6
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             d_consCF_738
             (coe
                C_mkCompiledFun_552
                (coe
                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v3)))
                (coe v5) (coe v7))
             (coe
                d_compileEntries_748 (coe v0) (coe v1)
                (coe
                   d_extendScope_716 (coe v2)
                   (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v3)) (coe v5))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-poly-p
d_ce'45'poly'45'p_782 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'poly'45'p_782 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("`" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_pfunName_104 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is more precise than its schema: the body also checks at "
                       ::
                       Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Once.Type.d_showType_36
                            (coe
                               MAlonzo.Code.Once.Internal.Type.Instance.d_arityOf_88
                               (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v3)))
                            (coe v6))
                         (". A signature states the body's own type: write the more precise one"
                          ::
                          Data.Text.Text)))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_ce'45'poly_786 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                du_checkOK_634
                (coe
                   MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6500
                   (coe
                      MAlonzo.Code.Once.Internal.Type.Instance.d_arityOf_88
                      (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v3)))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                      (coe
                         MAlonzo.Code.Once.Internal.Type.Instance.d_kindsOf_168
                         (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v3)))
                      (coe d_ctop_656 (coe v2)) (coe d_cpolys_662 (coe v2)))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_108 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Internal.Type.Instance.d_rigidOf_162
                      (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-poly
d_ce'45'poly_786 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'poly_786 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_pfunName_104 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text) v6)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_compileEntries_748 (coe v0) (coe v1)
             (coe d_addEntry_732 (coe v2) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule-aux
d_compileResolvedModule'45'aux_1016 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule'45'aux_1016 v0 v1 ~v2 v3
  = du_compileResolvedModule'45'aux_1016 v0 v1 v3
du_compileResolvedModule'45'aux_1016 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileResolvedModule'45'aux_1016 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             d_compileEntries_748 (coe v0) (coe v1) (coe d_emptyCScope_654)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_1034 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_1034 v0 v1 v2
  = coe
      du_compileResolvedModule'45'aux_1016 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v2))
-- Once.Compile.lw-entries
d_lw'45'entries_1042 ::
  T_CScope_638 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lw'45'entries_1042 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_114 v4
               -> coe
                    d_lw'45'fun_1044 (coe v0) (coe v4) (coe v3)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_92 (coe v4))
             MAlonzo.Code.Once.Parser.C_e'45'poly_116 v4
               -> coe
                    d_lw'45'entries_1042 (coe d_addEntry_732 (coe v0) (coe v4))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-fun
d_lw'45'fun_1044 ::
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  Bool -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lw'45'fun_1044 v0 v1 v2 v3
  = if coe v3
      then coe
             d_lw'45'prim_1046 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Parser.d_funType_88 (coe v1))
      else coe
             d_lw'45'mono_1048 (coe v0) (coe v1) (coe v2)
             (coe
                d_resolveFunType_608 (coe d_ctop_656 (coe v0))
                (coe d_cpolys_662 (coe v0))
                (coe MAlonzo.Code.Once.Parser.d_funType_88 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funBody_90 (coe v1)))
-- Once.Compile.lw-prim
d_lw'45'prim_1046 ::
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lw'45'prim_1046 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             d_lw'45'entries_1042
             (coe
                d_extendSig_724 (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v1)) (coe v4))
             (coe v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-mono
d_lw'45'mono_1048 ::
  T_CScope_638 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lw'45'mono_1048 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_lw'45'name_1072 (coe v1)
                (coe
                   d_lw'45'bodyM_1070
                   (coe MAlonzo.Code.Once.Parser.d_funType_88 (coe v1))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                      (coe d_ctop_656 (coe v0)) (coe d_cpolys_662 (coe v0)))
                   (coe MAlonzo.Code.Once.Parser.d_funBody_90 (coe v1)) (coe v4)))
             (coe
                d_lw'45'entries_1042
                (coe
                   d_extendScope_716 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v1)) (coe v4))
                (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-body
d_lw'45'body_1056 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_lw'45'body_1056 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v6 v7 v8 v9
               -> coe
                    ltInt (coe (0 :: Integer))
                    (coe
                       MAlonzo.Code.Once.Surface.LoopWarn.du_silentLoops_34 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Denotation.Realize.d_realize_22
                          (coe (0 :: Integer)) (coe v0) (coe v1) (coe v2) (coe v6)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-bodyI
d_lw'45'bodyI_1062 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> Bool
d_lw'45'bodyI_1062 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v5 v6 v7 v8 v9
               -> coe
                    ltInt (coe (0 :: Integer))
                    (coe
                       MAlonzo.Code.Once.Surface.LoopWarn.du_silentLoops_34 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_34
                          (coe (0 :: Integer)) (coe v0) (coe v1) (coe v5) (coe v6)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_100 v5
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-bodyM
d_lw'45'bodyM_1070 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_114 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> Bool
d_lw'45'bodyM_1070 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             d_lw'45'body_1056 (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6500
                (coe (0 :: Integer)) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_lw'45'bodyI_1062 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6490
                (coe (0 :: Integer)) (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lw-name
d_lw'45'name_1072 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  Bool -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lw'45'name_1072 v0 v1
  = if coe v1
      then coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.Parser.d_funName_86 (coe v0))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      else coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.silentRoundDefs-aux
d_silentRoundDefs'45'aux_1168 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_silentRoundDefs'45'aux_1168 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_lw'45'entries_1042 (coe d_emptyCScope_654) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.silentRoundDefs
d_silentRoundDefs_1172 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_silentRoundDefs_1172 v0
  = coe
      d_silentRoundDefs'45'aux_1168
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v0))
-- Once.Compile.compileModule
d_compileModule_1176 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_1176 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Once.Parser.Module.d_r_370
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_1022 (coe v2)))) in
    coe
      (let v4
             = MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
              -> coe
                   d_compileEntries_748 (coe v0) (coe v1) (coe d_emptyCScope_654)
                   (coe v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.emittedSyms
d_emittedSyms_1208 ::
  [T_CompiledFun_538] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms_1208 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                (coe d_cfName_546 (coe v1)))
             (coe d_emittedSyms_1208 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms-aux
d_moduleSyms'45'aux_1214 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms'45'aux_1214 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_emittedSyms_1208 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms
d_moduleSyms_1218 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms_1218 v0 v1 v2
  = coe
      d_moduleSyms'45'aux_1214
      (coe d_compileResolvedModule_1034 (coe v0) (coe v1) (coe v2))
-- Once.Compile.EffUU
d_EffUU_1228 :: Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_EffUU_1228 ~v0 = du_EffUU_1228
du_EffUU_1228 :: MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_EffUU_1228
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
         (coe MAlonzo.Code.Once.Spec.Grade.C_eff_44))
      (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
-- Once.Compile.mainEntry
d_mainEntry_1232 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_mainEntry_1232 ~v0 v1 = du_mainEntry_1232 v1
du_mainEntry_1232 ::
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.IR.T_IR_16
du_mainEntry_1232 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe
             MAlonzo.Code.Once.IR.C__'8728'__28
             (coe MAlonzo.Code.Once.IRTy.C_Void_18)
             (coe MAlonzo.Code.Once.IR.C_initial_76)
             (coe
                MAlonzo.Code.Once.IR.C_Call_146
                (MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe ("main" :: Data.Text.Text))))
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v8 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
               -> coe
                    MAlonzo.Code.Once.IR.C__'8728'__28
                    (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                    (coe MAlonzo.Code.Once.IR.C_initial_76)
                    (coe
                       MAlonzo.Code.Once.IR.C_Call_146
                       (MAlonzo.Code.Once.Spec.Name.d_bare_14
                          (coe ("main" :: Data.Text.Text))))
             MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
               -> coe
                    MAlonzo.Code.Once.IR.C_Call_146
                    (MAlonzo.Code.Once.Spec.Name.d_bare_14
                       (coe ("main" :: Data.Text.Text)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.findMain-here
d_findMain'45'here_1244 ::
  T_CompiledFun_538 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain'45'here_1244 ~v0 v1 v2 v3
  = du_findMain'45'here_1244 v1 v2 v3
du_findMain'45'here_1244 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
du_findMain'45'here_1244 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then case coe v6 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe du_mainEntry_1232 (coe v7))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe seq (coe v6) (coe v2)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.findMain
d_findMain_1260 ::
  [T_CompiledFun_538] -> Maybe MAlonzo.Code.Once.IR.T_IR_16
d_findMain_1260 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             du_findMain'45'here_1244
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                (coe d_cfName_546 (coe v1))
                (coe
                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe ("main" :: Data.Text.Text))))
             (coe
                MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__170
                (coe (0 :: Integer)) (coe d_cfType_548 (coe v1))
                (coe du_EffUU_1228))
             (coe d_findMain_1260 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToIR-aux
d_moduleToIR'45'aux_1266 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR'45'aux_1266 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_findMain_1260 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToIR
d_moduleToIR_1270 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_moduleToIR_1270 v0
  = coe
      d_moduleToIR'45'aux_1266
      (coe
         d_compileResolvedModule_1034 (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Compile.irFunOf
d_irFunOf_1274 ::
  T_CompiledFun_538 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_irFunOf_1274 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe d_cfName_546 (coe v0))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe d_dc_1282 (coe v0))))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe d_dc_1282 (coe v0)))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe d_dc_1282 (coe v0))))
-- Once.Compile._.dc
d_dc_1282 ::
  T_CompiledFun_538 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dc_1282 v0
  = coe
      d_directCallIR_84 (coe (0 :: Integer)) (coe d_cfType_548 (coe v0))
      (coe d_cfIR_550 (coe v0))
-- Once.Compile.tableOf-go
d_tableOf'45'go_1284 ::
  [T_CompiledFun_538] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf'45'go_1284 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             d_tableOf'45'go_1284 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe d_irFunOf_1274 (coe v2)) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.tableOf
d_tableOf_1294 ::
  [T_CompiledFun_538] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOf_1294 v0
  = coe
      d_tableOf'45'go_1284 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.tableOfResult
d_tableOfResult_1298 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tableOfResult_1298 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_tableOf_1294 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleTable
d_moduleTable_1302 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_moduleTable_1302 v0
  = coe
      d_tableOfResult_1298
      (coe
         d_compileResolvedModule_1034 (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Compile.programAt
d_programAt_1306 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_programAt_1306 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.Denotation.Program.C_irProgram_396 (coe v0)
                (coe v2))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleToProgram
d_moduleToProgram_1314 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  Maybe MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_moduleToProgram_1314 v0
  = coe
      d_programAt_1306 (coe d_moduleTable_1302 (coe v0))
      (coe d_moduleToIR_1270 (coe v0))
-- Once.Compile.rewrite-fun
d_rewrite'45'fun_1318 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_rewrite'45'fun_1318 v0
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
d_rewrite'45'table_1322 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_rewrite'45'table_1322 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_rewrite'45'fun_1318 (coe v1))
             (coe d_rewrite'45'table_1322 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.rewrite-program
d_rewrite'45'program_1328 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_rewrite'45'program_1328 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
      (coe
         d_rewrite'45'table_1322
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v0))))
-- Once.Compile.program-blocks
d_program'45'blocks_1332 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_program'45'blocks_1332 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_222
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
            (coe MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v0))))
      (coe
         du_table'45'blocks_1340
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0)))
-- Once.Compile._.table-blocks
d_table'45'blocks_1340 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_table'45'blocks_1340 ~v0 v1 = du_table'45'blocks_1340 v1
du_table'45'blocks_1340 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
du_table'45'blocks_1340 v0
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
             (coe du_table'45'blocks_1340 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.dedup-go
d_dedup'45'go_1346 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'go_1346 v0 v1
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
                    (coe d_dedup'45'go_1346 (coe v0) (coe v3))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe
                          d_dedup'45'go_1346
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v0))
                          (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.dedup-blocks
d_dedup'45'blocks_1360 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_dedup'45'blocks_1360
  = coe
      d_dedup'45'go_1346
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.block-symbol
d_block'45'symbol_1362 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'symbol_1362 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_62
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_188
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v0)))
-- Once.Compile.block-syms
d_block'45'syms_1366 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_block'45'syms_1366 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe
         d_dedup'45'blocks_1360
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_block'45'symbol_1362 (coe v1)) (coe v1)))
            (coe v0)))
-- Once.Compile.calls-of
d_calls'45'of_1372 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_calls'45'of_1372 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
         (coe MAlonzo.Code.Once.Denotation.Program.d_main_394 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Base.du_concatMap_246
         (coe
            (\ v1 ->
               MAlonzo.Code.Once.CCC.Codegen.NodesOK.d_leaf'45'syms_100
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v1))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v1))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v1))))
         (coe MAlonzo.Code.Once.Denotation.Program.d_table_392 (coe v0)))
-- Once.Compile.is-extern?
d_is'45'extern'63'_1382 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_is'45'extern'63'_1382 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
         (coe v1)
         (coe d_block'45'syms_1366 (coe d_program'45'blocks_1332 (coe v0))))
-- Once.Compile.externs-of
d_externs'45'of_1388 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_externs'45'of_1388 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_filter_648
      (coe d_is'45'extern'63'_1382 (coe v0))
      (coe d_calls'45'of_1372 (coe d_rewrite'45'program_1328 (coe v0)))
-- Once.Compile.prog-externs
d_prog'45'externs_1392 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_prog'45'externs_1392 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.Target.SymbolFresh.d_host'45'leave'45'symbol_164)
      (coe d_externs'45'of_1388 (coe v0))
-- Once.Compile.entry-owner
d_entry'45'owner_1396 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_entry'45'owner_1396
  = coe
      MAlonzo.Code.Once.Spec.Name.d_bare_14
      (coe ("0entry" :: Data.Text.Text))
-- Once.Compile.FileOf
d_FileOf_1398 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> ()
d_FileOf_1398 = erased
-- Once.Compile.printFile
d_printFile_1402 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printFile_1402 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.d_print_84
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.CCC.Target.RiscV64.File.d_print_84
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.image-of
d_image'45'of_1404 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_image'45'of_1404 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_program'45'image_36
      (coe d_entry'45'owner_1396)
      (coe d_rewrite'45'program_1328 (coe v0))
-- Once.Compile.blocks-x86-64
d_blocks'45'x86'45'64_1408 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'x86'45'64_1408 v0
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
         d_dedup'45'blocks_1360
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
            (coe d_program'45'blocks_1332 (coe v0))))
-- Once.Compile.emit-x86-64
d_emit'45'x86'45'64_1416 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.T_Image_12
d_emit'45'x86'45'64_1416 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_72
            (coe d_entry'45'owner_1396) (coe (0 :: Integer))
            (coe d_image'45'of_1404 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'x86'45'64_1408 (coe v0))
      (coe d_prog'45'externs_1392 (coe v0))
-- Once.Compile.blocks-x86-32
d_blocks'45'x86'45'32_1420 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'x86'45'32_1420 v0
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
         d_dedup'45'blocks_1360
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
            (coe d_program'45'blocks_1332 (coe v0))))
-- Once.Compile.emit-x86-32
d_emit'45'x86'45'32_1428 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.T_Image_12
d_emit'45'x86'45'32_1428 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace'45'cnt_122
            (coe d_entry'45'owner_1396) (coe (0 :: Integer))
            (coe d_image'45'of_1404 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'x86'45'32_1420 (coe v0))
      (coe d_prog'45'externs_1392 (coe v0))
-- Once.Compile.blocks-riscv64
d_blocks'45'riscv64_1432 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_blocks'45'riscv64_1432 v0
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
         d_dedup'45'blocks_1360
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
            (coe d_program'45'blocks_1332 (coe v0))))
-- Once.Compile.emit-riscv64
d_emit'45'riscv64_1440 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 ->
  MAlonzo.Code.Once.CCC.Target.RiscV64.File.T_Image_12
d_emit'45'riscv64_1440 v0
  = coe
      MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_mkImage_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace'45'cnt_152
            (coe d_entry'45'owner_1396) (coe (0 :: Integer))
            (coe d_image'45'of_1404 (coe v0))))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe d_blocks'45'riscv64_1432 (coe v0))
      (coe d_prog'45'externs_1392 (coe v0))
-- Once.Compile.emitProgram
d_emitProgram_1446 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386 -> AgdaAny
d_emitProgram_1446 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe d_emit'45'x86'45'64_1416
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe d_emit'45'x86'45'32_1428
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe d_emit'45'riscv64_1440
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.lib-image
d_lib'45'image_1448 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2252]
d_lib'45'image_1448 v0
  = coe
      MAlonzo.Code.Once.CCC.Codegen.ProgramImage.d_fns'45'image_20
      (coe (0 :: Integer)) (coe d_rewrite'45'table_1322 (coe v0))
-- Once.Compile.lib-program
d_lib'45'program_1452 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_386
d_lib'45'program_1452 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irProgram_396 (coe v0)
      (coe MAlonzo.Code.Once.IR.C_id_20)
-- Once.Compile.lib-blocks
d_lib'45'blocks_1456 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166]
d_lib'45'blocks_1456 v0
  = coe d_program'45'blocks_1332 (coe d_lib'45'program_1452 (coe v0))
-- Once.Compile.emitLibrary
d_emitLibrary_1462 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] -> AgdaAny
d_emitLibrary_1462 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.AbstractToX86.d_compile'45'trace'45'cnt_72
                   (coe d_entry'45'owner_1396) (coe (0 :: Integer))
                   (coe d_lib'45'image_1448 (coe v1))))
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
                   d_dedup'45'blocks_1360
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
                      (coe d_lib'45'blocks_1456 (coe v1)))))
             (coe d_externs'45'of_1388 (coe d_lib'45'program_1452 (coe v1)))
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe
             MAlonzo.Code.Once.CCC.Target.X86Z45Z32.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z32.AbstractToX86Z45Z32.d_compile'45'trace'45'cnt_122
                   (coe d_entry'45'owner_1396) (coe (0 :: Integer))
                   (coe d_lib'45'image_1448 (coe v1))))
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
                   d_dedup'45'blocks_1360
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
                      (coe d_lib'45'blocks_1456 (coe v1)))))
             (coe d_externs'45'of_1388 (coe d_lib'45'program_1452 (coe v1)))
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe
             MAlonzo.Code.Once.CCC.Target.RiscV64.File.C_mkImage_30
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   MAlonzo.Code.Once.CCC.Target.RiscV64.AbstractToRiscV.d_compile'45'trace'45'cnt_152
                   (coe d_entry'45'owner_1396) (coe (0 :: Integer))
                   (coe d_lib'45'image_1448 (coe v1))))
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
                   d_dedup'45'blocks_1360
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
                      (coe d_lib'45'blocks_1456 (coe v1)))))
             (coe d_externs'45'of_1388 (coe d_lib'45'program_1452 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emit-at
d_emit'45'at_1484 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  [T_CompiledFun_538] ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_emit'45'at_1484 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             d_emitProgram_1446 v0
             (coe
                MAlonzo.Code.Once.Denotation.Program.C_irProgram_396
                (coe d_tableOf_1294 (coe v1)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_emitLibrary_1462 (coe v0) (coe d_tableOf_1294 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emitFromCompiled
d_emitFromCompiled_1498 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_emitFromCompiled_1498 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                d_emit'45'at_1484 (coe v0) (coe v2) (coe d_findMain_1260 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.Stage
d_Stage_1508 = ()
data T_Stage_1508 = C_Parse_1510 | C_Check_1512 | C_Build_1514
-- Once.Compile.CompileResult
d_CompileResult_1516 = ()
data T_CompileResult_1516
  = C_Parsed_1518 [MAlonzo.Code.Once.Parser.T_FunInfo_76]
                  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_96] |
    C_Checked_1520 [T_CompiledFun_538] |
    C_Built_1522 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_1524 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.built-of
d_built'45'of_1528 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1516
d_built'45'of_1528 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_Error_1524 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe C_Built_1522 (coe d_printFile_1402 v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showFunInfo
d_showFunInfo_1538 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_76 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_1538 v0
  = let v1 = MAlonzo.Code.Once.Parser.d_funType_88 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_86 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" : " :: Data.Text.Text)
                   (MAlonzo.Code.Once.Type.d_showType_36
                      (coe (0 :: Integer)) (coe v2)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Parser.d_funName_86 (coe v0))
                (" : <inferred>" :: Data.Text.Text)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.showPolyFunInfo
d_showPolyFunInfo_1552 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_1552 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_104 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_134
            (coe MAlonzo.Code.Once.Parser.d_pfunType_106 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_1556 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_76] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_1556 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_1538 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_1556 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_1538 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_1564 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_96] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_1564 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_1552 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_1564 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_1552 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_1572 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1508 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_1516
d_compile_1572 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.Parser.d_parseStrict'45'at_56
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       MAlonzo.Code.Once.Parser.Module.du_pdwf'45'sk_308
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                          (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                          (coe (0 :: Integer)))
                       (coe
                          MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                          (coe
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                             (coe (0 :: Integer))))
                       (\ v5 v6 v7 ->
                          coe
                            MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                            (coe
                               MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                               (coe (0 :: Integer)))))))
              (coe
                 MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_26
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Parser.Module.d_r_370
                       (coe
                          MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
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
                             MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                             (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                             (coe (0 :: Integer)))
                          (coe
                             MAlonzo.Code.Once.Parser.Core.d_skipNewlines_10
                             (coe
                                MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                                (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                                (coe (0 :: Integer))))
                          (\ v5 v6 v7 ->
                             coe
                               MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_176
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.du_tokenize'45'WF_624
                                  (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4)
                                  (coe (0 :: Integer)))))))) in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
           -> coe C_Error_1524 (coe v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe C_Error_1524 (coe v8)
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> case coe v1 of
                          C_Parse_1510
                            -> coe
                                 C_Parsed_1518 (coe MAlonzo.Code.Once.Parser.d_funsOf_118 (coe v8))
                                 (coe MAlonzo.Code.Once.Parser.d_polysOf_126 (coe v8))
                          C_Check_1512
                            -> let v9
                                     = d_compileEntries_748
                                         (coe v0) (coe v2) (coe d_emptyCScope_654) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1524 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe C_Checked_1520 (coe v10)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_Build_1514
                            -> let v9
                                     = d_compileEntries_748
                                         (coe v0) (coe v2) (coe d_emptyCScope_654) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1524 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe
                                           d_built'45'of_1528 (coe v3)
                                           (coe d_emitFromCompiled_1498 (coe v3) (coe v9))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.cfm-check-emit
d_cfm'45'check'45'emit_1632 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1516
d_cfm'45'check'45'emit_1632 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_Error_1524 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe C_Checked_1520 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.litRangeError
d_litRangeError_1638 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_litRangeError_1638 v0 v1
  = coe
      du_badLit_1650 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Admissible.d_firstBadLit_104 (coe v0)
         (coe v1))
-- Once.Compile._.bits
d_bits_1648 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 -> Integer
d_bits_1648 v0 ~v1 = du_bits_1648 v0
du_bits_1648 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> Integer
du_bits_1648 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_64 (coe v0)
-- Once.Compile._.badLit
d_badLit_1650 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_badLit_1650 v0 ~v1 v2 = du_badLit_1650 v0 v2
du_badLit_1650 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_badLit_1650 v0 v1
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
                      (MAlonzo.Code.Once.Target.Arch.d_archName_72 (coe v0))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("'s signed " :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (coe
                               MAlonzo.Code.Data.Nat.Show.d_show_56 (coe du_bits_1648 (coe v0)))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("-bit range (-2^" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe
                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                        (coe du_bits_1648 (coe v0)) (1 :: Integer)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (" .. 2^" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (coe
                                           MAlonzo.Code.Data.Nat.Show.d_show_56
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                              (coe du_bits_1648 (coe v0)) (1 :: Integer)))
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
             (MAlonzo.Code.Once.Target.Arch.d_archName_72 (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-file-gated
d_cfm'45'file'45'gated_1658 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cfm'45'file'45'gated_1658 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       d_emitFromCompiled_1498 (coe v2)
                       (coe
                          d_compileEntries_748 (coe v0) (coe v1) (coe d_emptyCScope_654)
                          (coe v4)))
             else coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe d_litRangeError_1638 (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-file-ef
d_cfm'45'file'45'ef_1682 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cfm'45'file'45'ef_1682 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v4
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             d_cfm'45'file'45'gated_1658 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_72
                (coe v2) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFileFromModule
d_compileFileFromModule_1706 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFileFromModule_1706 v0 v1 v2 v3
  = coe
      d_cfm'45'file'45'ef_1682 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v3))
-- Once.Compile.cfm-stage-aux
d_cfm'45'stage'45'aux_1716 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1508 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  [MAlonzo.Code.Once.Parser.T_Entry_112] -> T_CompileResult_1516
d_cfm'45'stage'45'aux_1716 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      C_Parse_1510
        -> coe
             C_Parsed_1518 (coe MAlonzo.Code.Once.Parser.d_funsOf_118 (coe v5))
             (coe MAlonzo.Code.Once.Parser.d_polysOf_126 (coe v5))
      C_Check_1512
        -> coe
             d_cfm'45'check'45'emit_1632
             (coe
                d_compileEntries_748 (coe v0) (coe v2) (coe d_emptyCScope_654)
                (coe v5))
      C_Build_1514
        -> coe
             d_built'45'of_1528 (coe v3)
             (coe
                d_cfm'45'file'45'gated_1658 (coe v0) (coe v2) (coe v3) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_72
                   (coe v3) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-ef-aux
d_cfm'45'ef'45'aux_1748 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1508 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1516
d_cfm'45'ef'45'aux_1748 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe C_Error_1524 (coe v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_cfm'45'stage'45'aux_1716 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFromModule
d_compileFromModule_1774 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1508 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_20 ->
  T_CompileResult_1516
d_compileFromModule_1774 v0 v1 v2 v3 v4
  = coe
      d_cfm'45'ef'45'aux_1748 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_620 (coe v4))
