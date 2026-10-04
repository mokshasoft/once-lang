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
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.Machine.Rewrite
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.CCC.Codegen.EmittedWF
import qualified MAlonzo.Code.Once.CCC.Codegen.IRToTrace
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Admissible
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
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Target.RiscV64
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.X86Z45Z32
import qualified MAlonzo.Code.Once.Target.X86Z45Z64
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Principal
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Compile.validateMain
d_validateMain_4 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_validateMain_4 v0
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
d_directCallIR_14 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_directCallIR_14 v0 v1
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
d_FunCtx_44 :: ()
d_FunCtx_44 = erased
-- Once.Compile.emptyFunCtx
d_emptyFunCtx_46 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyFunCtx_46 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.Compile.extendFunCtx
d_extendFunCtx_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extendFunCtx_48 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe v0)
-- Once.Compile.compileFunBody-aux
d_compileFunBody'45'aux_64 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody'45'aux_64 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_compileFunBody'45'aux_64 v0 v1 v3 v4 v5 v6 v7 v8 v10
du_compileFunBody'45'aux_64 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody'45'aux_64 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Optimize.d_optimize_2662
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'10214'_'10215''7580'_38
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_978
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                             (coe v11) (coe v7)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                                (coe v7) (coe v4) (coe v5)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                   (coe v3))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0)
                                   (coe v1) (coe v7) (coe v11) (coe v10)))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_978
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_392 (coe v0))
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396 (coe v0))
                          (coe v11) (coe v7)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
                             (coe v7) (coe v4) (coe v5)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                (coe v3))
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
d_compileFunBody_114 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFunBody_114 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFunBody_114 v1 v2 v3 v4 v5 v6 v7
du_compileFunBody_114 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFunBody_114 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFunBody'45'aux_64
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer)) (coe v1) (coe v2))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6158
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe v1) (coe v2))
         (coe v6) (coe v5))
-- Once.Compile.compileFun-main-aux
d_compileFun'45'main'45'aux_136 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'main'45'aux_136 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'main'45'aux_136 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'main'45'aux_136 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'main'45'aux_136 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> coe v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             du_compileFunBody_114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFun-aux
d_compileFun'45'aux_176 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun'45'aux_176 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_compileFun'45'aux_176 v1 v2 v3 v4 v5 v6 v7 v8
du_compileFun'45'aux_176 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun'45'aux_176 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_compileFun'45'main'45'aux_136 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6) (coe d_validateMain_4 (coe v5))
      else coe
             du_compileFunBody_114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Compile.compileFun
d_compileFun_214 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileFun_214 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_compileFun_214 v1 v2 v3 v4 v5 v6 v7
du_compileFun_214 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileFun_214 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_compileFun'45'aux_176 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Compile.CompiledFun
d_CompiledFun_232 = ()
data T_CompiledFun_232
  = C_mkCompiledFun_250 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                        MAlonzo.Code.Once.Type.T_Type_108 MAlonzo.Code.Once.IR.T_IR_16 Bool
-- Once.Compile.CompiledFun.cfName
d_cfName_242 ::
  T_CompiledFun_232 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_cfName_242 v0
  = case coe v0 of
      C_mkCompiledFun_250 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfType
d_cfType_244 ::
  T_CompiledFun_232 -> MAlonzo.Code.Once.Type.T_Type_108
d_cfType_244 v0
  = case coe v0 of
      C_mkCompiledFun_250 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIR
d_cfIR_246 :: T_CompiledFun_232 -> MAlonzo.Code.Once.IR.T_IR_16
d_cfIR_246 v0
  = case coe v0 of
      C_mkCompiledFun_250 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CompiledFun.cfIsPrimitive
d_cfIsPrimitive_248 :: T_CompiledFun_232 -> Bool
d_cfIsPrimitive_248 v0
  = case coe v0 of
      C_mkCompiledFun_250 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildFunCtx
d_buildFunCtx_252 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildFunCtx_252 v0
  = case coe v0 of
      [] -> coe d_emptyFunCtx_46
      (:) v1 v2
        -> let v3 = MAlonzo.Code.Once.Parser.d_funType_108 (coe v1) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                  -> coe
                       d_extendFunCtx_48 (coe d_buildFunCtx_252 (coe v2))
                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v4)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe d_buildFunCtx_252 (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.buildPolyCtx
d_buildPolyCtx_272 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_buildPolyCtx_272 v0
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
             (coe d_buildPolyCtx_272 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.inferType-validate
d_inferType'45'validate_278 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType'45'validate_278 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_6166
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
d_inferType_314 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_inferType_314 v0 v1 v2
  = let v3
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe
                 MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6150
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                    (coe v0) (coe v1))
                 (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v4 v5 v6 v7 v8
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_90 v4
           -> coe
                d_inferType'45'validate_278
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                   (coe v0) (coe v1))
                (coe v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("Cannot infer type: " :: Data.Text.Text)
                   (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_92 (coe v4)))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Principal.d_principalGround_2134
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                      (coe v0) (coe v1))
                   (coe v2))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.resolveFunType
d_resolveFunType_342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_resolveFunType_342 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe d_inferType_314 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.parseSourceToModule
d_parseSourceToModule_358 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_parseSourceToModule_358
  = coe MAlonzo.Code.Once.Parser.d_parseStrict_72
-- Once.Compile.seqCheck
d_seqCheck_360 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_seqCheck_360 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.checkOK
d_checkOK_372 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_checkOK_372 ~v0 ~v1 ~v2 v3 = du_checkOK_372 v3
du_checkOK_372 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_checkOK_372 v0
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
d_CScope_376 = ()
data T_CScope_376
  = C_cscope_386 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Compile.CScope.cimps
d_cimps_382 ::
  T_CScope_376 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cimps_382 v0
  = case coe v0 of
      C_cscope_386 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.CScope.ctele
d_ctele_384 ::
  T_CScope_376 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_ctele_384 v0
  = case coe v0 of
      C_cscope_386 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.emptyCScope
d_emptyCScope_388 :: T_CScope_376
d_emptyCScope_388
  = coe
      C_cscope_386 (coe d_emptyFunCtx_46)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Compile.telePolys
d_telePolys_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116]
d_telePolys_390
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
-- Once.Compile.cpolys
d_cpolys_392 ::
  T_CScope_376 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cpolys_392 v0
  = coe
      d_buildPolyCtx_272 (coe d_telePolys_390 (d_ctele_384 (coe v0)))
-- Once.Compile.declImps
d_declImps_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_declImps_396 v0 v1
  = case coe v0 of
      [] -> coe d_emptyFunCtx_46
      (:) v2 v3
        -> coe
             d_declImps'45'aux_402 (coe v2) (coe v3) (coe v1)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe
                   MAlonzo.Code.Once.Parser.d_pfunName_124
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.declImps-aux
d_declImps'45'aux_402 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_declImps'45'aux_402 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))
             else coe seq (coe v5) (coe d_declImps_396 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.extendScope
d_extendScope_424 ::
  T_CScope_376 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CScope_376
d_extendScope_424 v0 v1 v2
  = coe
      C_cscope_386
      (coe
         d_extendFunCtx_48 (coe d_cimps_382 (coe v0)) (coe v1) (coe v2))
      (coe d_ctele_384 (coe v0))
-- Once.Compile.addEntry
d_addEntry_432 ::
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 -> T_CScope_376
d_addEntry_432 v0 v1
  = coe
      C_cscope_386 (coe d_cimps_382 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
            (coe d_cimps_382 (coe v0)))
         (coe d_ctele_384 (coe v0)))
-- Once.Compile.consCF
d_consCF_438 ::
  T_CompiledFun_232 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consCF_438 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileEntries
d_compileEntries_448 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileEntries_448 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    d_ce'45'fun_452 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    d_ce'45'poly_482 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe
                       du_checkOK_372
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6158
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                             (coe d_cimps_382 (coe v2)) (coe d_cpolys_392 (coe v2)))
                          (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v6))
                          (coe
                             MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v6)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-fun
d_ce'45'fun_452 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'fun_452 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             d_ce'45'prim_456 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
      else coe
             d_ce'45'mono_466 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                d_resolveFunType_342 (coe d_cimps_382 (coe v2))
                (coe d_cpolys_392 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v3))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v3)))
-- Once.Compile.ce-prim
d_ce'45'prim_456 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim_456 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_ce'45'prim'45'conc_462 (coe v0) (coe v1) (coe v2) (coe v3)
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
d_ce'45'prim'45'conc_462 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'prim'45'conc_462 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                      -> coe
                           d_consCF_438
                           (coe
                              C_mkCompiledFun_250
                              (coe
                                 MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)))
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_978
                                 (coe (0 :: Integer))
                                 (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe (0 :: Integer)))
                                 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                    (MAlonzo.Code.Once.CanonicalName.d_bare_12
                                       (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)))
                                    v9))
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                           (coe
                              d_compileEntries_448 (coe v0) (coe v1)
                              (coe
                                 d_extendScope_424 (coe v2)
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v5))
                              (coe v4))
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
d_ce'45'mono_466 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono_466 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v5
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_ce'45'mono'45'g_472 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-mono-g
d_ce'45'mono'45'g_472 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'g_472 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             d_ce'45'mono'45'ir_478 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                du_compileFun_214 (coe v1) (coe d_cimps_382 (coe v2))
                (coe d_cpolys_392 (coe v2))
                (coe d_declImps_396 (coe d_ctele_384 (coe v2)))
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
d_ce'45'mono'45'ir_478 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'mono'45'ir_478 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v6
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             d_consCF_438
             (coe
                C_mkCompiledFun_250
                (coe
                   MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)))
                (coe v5) (coe v7)
                (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v3)))
             (coe
                d_compileEntries_448 (coe v0) (coe v1)
                (coe
                   d_extendScope_424 (coe v2)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v3)) (coe v5))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.ce-poly
d_ce'45'poly_482 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_ce'45'poly_482 v0 v1 v2 v3 v4 v5
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
             d_compileEntries_448 (coe v0) (coe v1)
             (coe d_addEntry_432 (coe v2) (coe v3)) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule-aux
d_compileResolvedModule'45'aux_700 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule'45'aux_700 v0 v1 ~v2 v3
  = du_compileResolvedModule'45'aux_700 v0 v1 v3
du_compileResolvedModule'45'aux_700 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_compileResolvedModule'45'aux_700 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             d_compileEntries_448 (coe v0) (coe v1) (coe d_emptyCScope_388)
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileResolvedModule
d_compileResolvedModule_718 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileResolvedModule_718 v0 v1 v2
  = coe
      du_compileResolvedModule'45'aux_700 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v2))
         (coe v2))
-- Once.Compile.compileModule
d_compileModule_726 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_compileModule_726 v0 v1 v2
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
                   d_compileEntries_448 (coe v0) (coe v1) (coe d_emptyCScope_388)
                   (coe v5)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Compile.emittedSyms-cons
d_emittedSyms'45'cons_760 ::
  Bool ->
  T_CompiledFun_232 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms'45'cons_760 v0 v1 v2
  = if coe v0
      then coe v2
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
                (coe d_cfName_242 (coe v1)))
             (coe v2)
-- Once.Compile.emittedSyms
d_emittedSyms_770 ::
  [T_CompiledFun_232] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_emittedSyms_770 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_emittedSyms'45'cons_760 (coe d_cfIsPrimitive_248 (coe v1))
             (coe v1) (coe d_emittedSyms_770 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms-aux
d_moduleSyms'45'aux_776 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms'45'aux_776 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_emittedSyms_770 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSyms
d_moduleSyms_780 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_moduleSyms_780 v0 v1 v2
  = coe
      d_moduleSyms'45'aux_776
      (coe d_compileResolvedModule_718 (coe v0) (coe v1) (coe v2))
-- Once.Compile.archTarget
d_archTarget_788 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Target.T_Target_4
d_archTarget_788 v0
  = case coe v0 of
      MAlonzo.Code.Once.Target.Arch.C_x86'45'64_8
        -> coe MAlonzo.Code.Once.Target.X86Z45Z64.d_x86'45'64_52
      MAlonzo.Code.Once.Target.Arch.C_x86'45'32_10
        -> coe MAlonzo.Code.Once.Target.X86Z45Z32.d_x86'45'32_38
      MAlonzo.Code.Once.Target.Arch.C_riscv64_12
        -> coe MAlonzo.Code.Once.Target.RiscV64.d_riscv64_42
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFunWithTarget
d_compileFunWithTarget_790 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunWithTarget_790 v0 v1 v2
  = let v3 = d_cfIsPrimitive_248 (coe v2) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe ("" :: Data.Text.Text))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         else coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Target.d_irToAsm_26 v0 (d_cfName_242 (coe v2)) v1
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v2))
                               (coe d_cfIR_246 (coe v2)))))
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                  (coe d_cfIR_246 (coe v2))))))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                     (coe d_cfIR_246 (coe v2)))))
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                        (coe d_cfIR_246 (coe v2))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                     (coe d_cfIR_246 (coe v2)))))))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe
                         MAlonzo.Code.Once.Target.d_functionPrologue_30 v0
                         (d_cfName_242 (coe v2)))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Once.Target.d_irToAsm_26 v0 (d_cfName_242 (coe v2)) v1
                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                        (coe d_cfIR_246 (coe v2)))))
                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                           (coe d_cfIR_246 (coe v2))))))
                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                              (coe d_cfIR_246 (coe v2)))))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                                 (coe d_cfIR_246 (coe v2))))))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                              (coe d_cfIR_246 (coe v2)))))))))
                         (MAlonzo.Code.Once.Target.d_functionEpilogue_32 (coe v0))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                  (coe d_cfIR_246 (coe v2)))))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                     (coe d_cfIR_246 (coe v2))))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v2))
                                  (coe d_cfIR_246 (coe v2)))))))))
-- Once.Compile.compileAllWithTarget
d_compileAllWithTarget_824 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_232] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_compileAllWithTarget_824 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_834 (coe v0))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe ("" :: Data.Text.Text))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
               (coe v1))))
      (coe
         MAlonzo.Code.Once.Target.d_emitArithBlocks_34 v0
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Data.List.Base.du_foldl_230 (coe du_step_834 (coe v0))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe ("" :: Data.Text.Text))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe v1)))))
-- Once.Compile._.step
d_step_834 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  [T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_834 v0 ~v1 v2 v3 = du_step_834 v0 v2 v3
du_step_834 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_834 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            d_compileFunWithTarget_790 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     d_compileFunWithTarget_790 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2)))))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     d_compileFunWithTarget_790 (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                     (coe v2))))))
-- Once.Compile.funLabels-cons
d_funLabels'45'cons_856 ::
  Bool ->
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funLabels'45'cons_856 v0 v1 v2 v3
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Target.d_irToAsm_26 v1 (d_cfName_242 (coe v3)) v2
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            d_directCallIR_14 (coe d_cfType_244 (coe v3))
                            (coe d_cfIR_246 (coe v3)))))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3))))))
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))))))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.EmittedWF.d_labels'45'def_8
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'linked'45'from_864
                      (coe d_cfName_242 (coe v3))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3)))))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3))))))
                      (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3)))))
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                        (coe d_cfIR_246 (coe v3))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))))))
-- Once.Compile.funLabels
d_funLabels_878 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funLabels_878 v0 v1 v2
  = coe
      d_funLabels'45'cons_856 (coe d_cfIsPrimitive_248 (coe v2)) (coe v0)
      (coe v1) (coe v2)
-- Once.Compile.emittedLabels
d_emittedLabels_886 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  [T_CompiledFun_232] -> [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_emittedLabels_886 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_funLabels_878 (coe v0) (coe v1) (coe v3)))
             (coe
                d_emittedLabels_886 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_funLabels_878 (coe v0) (coe v1) (coe v3)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleLabels-aux
d_moduleLabels'45'aux_900 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_moduleLabels'45'aux_900 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe d_emittedLabels_886 (coe v0) (coe (0 :: Integer)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleLabels
d_moduleLabels_908 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_moduleLabels_908 v0 v1 v2 v3
  = coe
      d_moduleLabels'45'aux_900 (coe d_archTarget_788 (coe v0))
      (coe d_compileResolvedModule_718 (coe v1) (coe v2) (coe v3))
-- Once.Compile.funLabelRefs-cons
d_funLabelRefs'45'cons_918 ::
  Bool ->
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funLabelRefs'45'cons_918 v0 v1 v2 v3
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Target.d_irToAsm_26 v1 (d_cfName_242 (coe v3)) v2
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            d_directCallIR_14 (coe d_cfType_244 (coe v3))
                            (coe d_cfIR_246 (coe v3)))))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3))))))
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))))))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.EmittedWF.d_labels'45'ref_26
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'linked'45'from_864
                      (coe d_cfName_242 (coe v3))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3)))))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3))))))
                      (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3)))))
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                        (coe d_cfIR_246 (coe v3))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))))))
-- Once.Compile.funLabelRefs
d_funLabelRefs_940 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funLabelRefs_940 v0 v1 v2
  = coe
      d_funLabelRefs'45'cons_918 (coe d_cfIsPrimitive_248 (coe v2))
      (coe v0) (coe v1) (coe v2)
-- Once.Compile.emittedLabelRefs
d_emittedLabelRefs_948 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  [T_CompiledFun_232] -> [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_emittedLabelRefs_948 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_funLabelRefs_940 (coe v0) (coe v1) (coe v3)))
             (coe
                d_emittedLabelRefs_948 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_funLabelRefs_940 (coe v0) (coe v1) (coe v3)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleLabelRefs-aux
d_moduleLabelRefs'45'aux_962 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_moduleLabelRefs'45'aux_962 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             d_emittedLabelRefs_948 (coe v0) (coe (0 :: Integer)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleLabelRefs
d_moduleLabelRefs_970 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28]
d_moduleLabelRefs_970 v0 v1 v2 v3
  = coe
      d_moduleLabelRefs'45'aux_962 (coe d_archTarget_788 (coe v0))
      (coe d_compileResolvedModule_718 (coe v1) (coe v2) (coe v3))
-- Once.Compile.funSyms-cons
d_funSyms'45'cons_980 ::
  Bool ->
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funSyms'45'cons_980 v0 v1 v2 v3
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      else coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   MAlonzo.Code.Once.Target.d_irToAsm_26 v1 (d_cfName_242 (coe v3)) v2
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            d_directCallIR_14 (coe d_cfType_244 (coe v3))
                            (coe d_cfIR_246 (coe v3)))))
                   (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3))))))
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))
                         (coe
                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3)))))))))
             (coe
                MAlonzo.Code.Once.CCC.Codegen.EmittedWF.d_syms'45'ref_86
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.CCC.Codegen.IRToTrace.d_ir'45'to'45'linked'45'from_864
                      (coe d_cfName_242 (coe v3))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v3))
                               (coe d_cfIR_246 (coe v3)))))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                  (coe d_cfIR_246 (coe v3))))))
                      (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                         (coe
                            MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3)))))
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                        (coe d_cfIR_246 (coe v3))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     d_directCallIR_14 (coe d_cfType_244 (coe v3))
                                     (coe d_cfIR_246 (coe v3))))))))))
-- Once.Compile.funSyms
d_funSyms_1002 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  T_CompiledFun_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_funSyms_1002 v0 v1 v2
  = coe
      d_funSyms'45'cons_980 (coe d_cfIsPrimitive_248 (coe v2)) (coe v0)
      (coe v1) (coe v2)
-- Once.Compile.emittedSymRefs
d_emittedSymRefs_1010 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  Integer ->
  [T_CompiledFun_232] ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_emittedSymRefs_1010 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe d_funSyms_1002 (coe v0) (coe v1) (coe v3)))
             (coe
                d_emittedSymRefs_1010 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe d_funSyms_1002 (coe v0) (coe v1) (coe v3)))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSymRefs-aux
d_moduleSymRefs'45'aux_1024 ::
  MAlonzo.Code.Once.Target.T_Target_4 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_moduleSymRefs'45'aux_1024 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe d_emittedSymRefs_1010 (coe v0) (coe (0 :: Integer)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSymRefs
d_moduleSymRefs_1032 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_moduleSymRefs_1032 v0 v1 v2 v3
  = coe
      d_moduleSymRefs'45'aux_1024 (coe d_archTarget_788 (coe v0))
      (coe d_compileResolvedModule_718 (coe v1) (coe v2) (coe v3))
-- Once.Compile.funBlockSyms-cons
d_funBlockSyms'45'cons_1042 ::
  Bool ->
  T_CompiledFun_232 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_funBlockSyms'45'cons_1042 v0 v1
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      else coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_cfName_242 (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du_map_22
                (coe
                   (\ v2 ->
                      MAlonzo.Code.Once.CanonicalName.d_bare_12
                        (coe
                           MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_348
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_134 (coe v2))
                           (coe
                              MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_138 (coe v2)))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      MAlonzo.Code.Once.Arith.Machine.Rewrite.d_rewrite'45'ir_202
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v1))
                               (coe d_cfIR_246 (coe v1)))))
                      (coe
                         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe
                                  d_directCallIR_14 (coe d_cfType_244 (coe v1))
                                  (coe d_cfIR_246 (coe v1))))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                            (coe
                               d_directCallIR_14 (coe d_cfType_244 (coe v1))
                               (coe d_cfIR_246 (coe v1))))))))
-- Once.Compile.emittedSymDefs
d_emittedSymDefs_1054 ::
  [T_CompiledFun_232] ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_emittedSymDefs_1054 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_funBlockSyms'45'cons_1042 (coe d_cfIsPrimitive_248 (coe v1))
                (coe v1))
             (coe d_emittedSymDefs_1054 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSymDefs-aux
d_moduleSymDefs'45'aux_1060 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_moduleSymDefs'45'aux_1060 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe d_emittedSymDefs_1054 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.moduleSymDefs
d_moduleSymDefs_1064 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_moduleSymDefs_1064 v0 v1 v2
  = coe
      d_moduleSymDefs'45'aux_1060
      (coe d_compileResolvedModule_718 (coe v0) (coe v1) (coe v2))
-- Once.Compile.Stage
d_Stage_1072 = ()
data T_Stage_1072 = C_Parse_1074 | C_Check_1076 | C_Build_1078
-- Once.Compile.CompileResult
d_CompileResult_1080 = ()
data T_CompileResult_1080
  = C_Parsed_1082 [MAlonzo.Code.Once.Parser.T_FunInfo_96]
                  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] |
    C_Checked_1084 [T_CompiledFun_232] |
    C_Built_1086 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Error_1088 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Once.Compile.showFunInfo
d_showFunInfo_1090 ::
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfo_1090 v0
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
d_showPolyFunInfo_1104 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfo_1104 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (" : " :: Data.Text.Text)
         (MAlonzo.Code.Once.Type.d_showPolyType_440
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0))))
-- Once.Compile.showFunInfos
d_showFunInfos_1108 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showFunInfos_1108 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showFunInfo_1090 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showFunInfos_1108 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showFunInfo_1090 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.showPolyFunInfos
d_showPolyFunInfos_1116 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPolyFunInfos_1116 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (d_showPolyFunInfo_1104 (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        ("\n" :: Data.Text.Text) (d_showPolyFunInfos_1116 (coe v2))) in
           coe
             (case coe v2 of
                [] -> coe d_showPolyFunInfo_1104 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compile
d_compile_1124 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1072 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CompileResult_1080
d_compile_1124 v0 v1 v2 v3 v4
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
                          MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
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
                             MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
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
           -> coe C_Error_1088 (coe v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> let v7
                    = MAlonzo.Code.Once.Parser.d_extractFunctions_572
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v6))
                        (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe C_Error_1088 (coe v8)
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> case coe v1 of
                          C_Parse_1074
                            -> coe
                                 C_Parsed_1082 (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v8))
                                 (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v8))
                          C_Check_1076
                            -> let v9
                                     = d_compileEntries_448
                                         (coe v0) (coe v2) (coe d_emptyCScope_388) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1088 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe C_Checked_1084 (coe v10)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_Build_1078
                            -> let v9
                                     = d_compileEntries_448
                                         (coe v0) (coe v2) (coe d_emptyCScope_388) (coe v8) in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                      -> coe C_Error_1088 (coe v10)
                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                      -> coe
                                           C_Built_1086
                                           (coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (MAlonzo.Code.Once.Target.d_asmHeader_28
                                                 (coe d_archTarget_788 (coe v3)))
                                              (d_compileAllWithTarget_824
                                                 (coe d_archTarget_788 (coe v3)) (coe v10)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Compile.cfm-build-emit
d_cfm'45'build'45'emit_1188 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1080
d_cfm'45'build'45'emit_1188 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe C_Error_1088 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             C_Built_1086
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (MAlonzo.Code.Once.Target.d_asmHeader_28
                   (coe d_archTarget_788 (coe v0)))
                (d_compileAllWithTarget_824
                   (coe d_archTarget_788 (coe v0)) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-check-emit
d_cfm'45'check'45'emit_1200 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1080
d_cfm'45'check'45'emit_1200 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe C_Error_1088 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe C_Checked_1084 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.litRangeError
d_litRangeError_1206 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_litRangeError_1206 v0 v1
  = coe
      du_badLit_1218 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.Admissible.d_firstBadLit_106 (coe v0)
         (coe v1))
-- Once.Compile._.bits
d_bits_1216 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> Integer
d_bits_1216 v0 ~v1 = du_bits_1216 v0
du_bits_1216 :: MAlonzo.Code.Once.Target.Arch.T_Arch_6 -> Integer
du_bits_1216 v0
  = coe
      MAlonzo.Code.Once.Target.Arch.d_arch'45'int'45'bits_80 (coe v0)
-- Once.Compile._.badLit
d_badLit_1218 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_badLit_1218 v0 ~v1 v2 = du_badLit_1218 v0 v2
du_badLit_1218 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_badLit_1218 v0 v1
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
                               MAlonzo.Code.Data.Nat.Show.d_show_56 (coe du_bits_1216 (coe v0)))
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("-bit range (-2^" :: Data.Text.Text)
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  (coe
                                     MAlonzo.Code.Data.Nat.Show.d_show_56
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                        (coe du_bits_1216 (coe v0)) (1 :: Integer)))
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     (" .. 2^" :: Data.Text.Text)
                                     (coe
                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                        (coe
                                           MAlonzo.Code.Data.Nat.Show.d_show_56
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                              (coe du_bits_1216 (coe v0)) (1 :: Integer)))
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
-- Once.Compile.cfm-build-gated
d_cfm'45'build'45'gated_1226 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_CompileResult_1080
d_cfm'45'build'45'gated_1226 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       d_cfm'45'build'45'emit_1188 (coe v2)
                       (coe
                          d_compileEntries_448 (coe v0) (coe v1) (coe d_emptyCScope_388)
                          (coe v4)))
             else coe
                    seq (coe v7)
                    (coe C_Error_1088 (coe d_litRangeError_1206 (coe v2) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-stage-aux
d_cfm'45'stage'45'aux_1248 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1072 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> T_CompileResult_1080
d_cfm'45'stage'45'aux_1248 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      C_Parse_1074
        -> coe
             C_Parsed_1082 (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v5))
             (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v5))
      C_Check_1076
        -> coe
             d_cfm'45'check'45'emit_1200
             (coe
                d_compileEntries_448 (coe v0) (coe v2) (coe d_emptyCScope_388)
                (coe v5))
      C_Build_1078
        -> coe
             d_cfm'45'build'45'gated_1226 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
                (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.cfm-ef-aux
d_cfm'45'ef'45'aux_1280 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1072 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_CompileResult_1080
d_cfm'45'ef'45'aux_1280 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe C_Error_1088 (coe v6)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_cfm'45'stage'45'aux_1248 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Compile.compileFromModule
d_compileFromModule_1306 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  T_Stage_1072 ->
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  T_CompileResult_1080
d_compileFromModule_1306 v0 v1 v2 v3 v4
  = coe
      d_cfm'45'ef'45'aux_1280 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v4))
         (coe v4))
