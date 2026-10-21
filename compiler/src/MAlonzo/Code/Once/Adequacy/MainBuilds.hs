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

module MAlonzo.Code.Once.Adequacy.MainBuilds where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Principal
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Honest
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.MainBuilds.cfb-aux-doOpt
d_cfb'45'aux'45'doOpt_30 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'aux'45'doOpt_30 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 ~v11
  = du_cfb'45'aux'45'doOpt_30 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_cfb'45'aux'45'doOpt_30 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'aux'45'doOpt_30 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v11 v12 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v2)
                       (coe
                          MAlonzo.Code.Once.Optimize.d_optimize_1248
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))))
                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v7))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0))
                             (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                             (coe v11) (coe v7)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                                (coe v7) (coe v4) (coe v5)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v3)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0)
                                   (coe v1) (coe v7) (coe v11) (coe v10)))))
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v0))
                          (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0))
                          (coe v11) (coe v7)
                          (coe
                             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                             (coe v7) (coe v4) (coe v5)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v3)))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.Denotation.Realize.d_realize_20 (coe v0) (coe v1)
                                (coe v7) (coe v11) (coe v10)))))
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfb-doOpt
d_cfb'45'doOpt_84 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6
du_cfb'45'doOpt_84 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfb'45'aux'45'doOpt_30
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1))
         (coe v2)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1)))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6328
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v1) (coe v2))
         (coe v6) (coe v5))
-- Once.Adequacy.MainBuilds.cfun-main-aux-doOpt
d_cfun'45'main'45'aux'45'doOpt_122 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'main'45'aux'45'doOpt_122 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'main'45'aux'45'doOpt_122 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'main'45'aux'45'doOpt_122 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'main'45'aux'45'doOpt_122 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (coe
         du_cfb'45'doOpt_84 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6))
-- Once.Adequacy.MainBuilds.cfun-aux-doOpt
d_cfun'45'aux'45'doOpt_176 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'aux'45'doOpt_176 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_cfun'45'main'45'aux'45'doOpt_122 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v5))
      else coe
             du_cfb'45'doOpt_84 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Adequacy.MainBuilds.cfun-doOpt
d_cfun'45'doOpt_228 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6
du_cfun'45'doOpt_228 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfun'45'aux'45'doOpt_176 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.MainBuilds.cfbI-doOpt
d_cfbI'45'doOpt_264 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfbI'45'doOpt_264 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfbI'45'doOpt_264 v0 v1 v2 v3 v4 v5 v6
du_cfbI'45'doOpt_264 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfbI'45'doOpt_264 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_aux_310 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6320
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v1) (coe v2))
         (coe v6))
-- Once.Adequacy.MainBuilds._.at
d_at_298 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_298 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8 v9 v10 v11 v12 ~v13 ~v14
  = du_at_298 v0 v1 v2 v3 v4 v6 v9 v10 v11 v12
du_at_298 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_298 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> coe
             seq (coe v10)
             (coe
                seq (coe v11)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0)
                      (coe
                         MAlonzo.Code.Once.Optimize.d_optimize_1248
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                               (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)))
                         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v6))
                         (coe
                            MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                            (coe (0 :: Integer))
                            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v7) (coe v6)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                               (coe v6) (coe v2) (coe v3)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1)))
                               (coe (0 :: Integer))
                               (coe
                                  MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                  (coe
                                     MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                     (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                     (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1))
                                     (coe v2)
                                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1)))
                                  (coe v5) (coe v6) (coe v7) (coe v8)))))
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                         (coe (0 :: Integer))
                         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v7) (coe v6)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                            (coe v6) (coe v2) (coe v3)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1)))
                            (coe (0 :: Integer))
                            (coe
                               MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                               (coe
                                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                  (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v1))
                                  (coe v2)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v1)))
                               (coe v5) (coe v6) (coe v7) (coe v8)))))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds._.aux
d_aux_310 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_310 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_aux_310 v0 v1 v2 v3 v4 v5 v6 v9
du_aux_310 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_310 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v10 v11 v12 v13 v14
               -> coe
                    du_at_298 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                    (coe v10) (coe v11) (coe v9)
                    (coe
                       MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v10)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfunI-doOpt
d_cfunI'45'doOpt_336 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfunI'45'doOpt_336 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfunI'45'doOpt_336 v0 v1 v2 v3 v4 v5 v6
du_cfunI'45'doOpt_336 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfunI'45'doOpt_336 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_aux_374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.MainBuilds._.main
d_main_364 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main_364 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_main_364 v0 v1 v2 v3 v4 v5 v6 v9
du_main_364 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main_364 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v7)
      (coe
         du_cfbI'45'doOpt_264 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6))
-- Once.Adequacy.MainBuilds._.aux
d_aux_374 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_374 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_aux_374 v0 v1 v2 v3 v4 v5 v6 v9
du_aux_374 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_374 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_main_364 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v5))
      else coe
             du_cfbI'45'doOpt_264 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Adequacy.MainBuilds.cfunM-doOpt
d_cfunM'45'doOpt_400 ::
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfunM'45'doOpt_400 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
                coe du_cfun'45'doOpt_228 v2 v3 v4 v5 v6 v7 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
                coe du_cfunI'45'doOpt_336 v1 v2 v3 v4 v5 v6 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-doOpt
d_ce'45'doOpt_412 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'doOpt_412 v0 v1 v2 v3 ~v4 = du_ce'45'doOpt_412 v0 v1 v2 v3
du_ce'45'doOpt_412 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'doOpt_412 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    du_ce'45'fun'45'doOpt_428 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
                    (coe v3)
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    du_ce'45'poly'45'p'45'doOpt_512 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Compile.d_firstChecking_28
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                          (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                          (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1)))
                       (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v6))
                       (coe
                          MAlonzo.Code.Once.Lang.Principal.d_below_10
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v6)))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-fun-doOpt
d_ce'45'fun'45'doOpt_428 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'fun'45'doOpt_428 v0 v1 v2 v3 v4 v5 ~v6
  = du_ce'45'fun'45'doOpt_428 v0 v1 v2 v3 v4 v5
du_ce'45'fun'45'doOpt_428 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'fun'45'doOpt_428 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             du_ce'45'prim'45'doOpt_444 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2)) (coe v5)
      else coe
             du_ce'45'mono'45'doOpt_460 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_594
                (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
-- Once.Adequacy.MainBuilds.ce-prim-doOpt
d_ce'45'prim'45'doOpt_444 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'prim'45'doOpt_444 v0 v1 v2 v3 v4 v5 ~v6
  = du_ce'45'prim'45'doOpt_444 v0 v1 v2 v3 v4 v5
du_ce'45'prim'45'doOpt_444 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'prim'45'doOpt_444 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_conc_610 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v6))
             (coe MAlonzo.Code.Once.Lang.Type.Honest.d_honest'63'_202 (coe v6))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v6))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-mono-doOpt
d_ce'45'mono'45'doOpt_460 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'mono'45'doOpt_460 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_ce'45'mono'45'doOpt_460 v0 v1 v2 v3 v4
du_ce'45'mono'45'doOpt_460 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'mono'45'doOpt_460 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_ce'45'mono'45'p'45'doOpt_478 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v5)
             (coe
                MAlonzo.Code.Once.Compile.d_firstChecking_28
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                   (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                   (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1)))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
                (coe MAlonzo.Code.Once.Lang.Principal.d_below_10 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-mono-p-doOpt
d_ce'45'mono'45'p'45'doOpt_478 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'mono'45'p'45'doOpt_478 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_ce'45'mono'45'p'45'doOpt_478 v0 v1 v2 v3 v4 v5
du_ce'45'mono'45'p'45'doOpt_478 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'mono'45'p'45'doOpt_478 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (coe
         du_ce'45'mono'45'g'45'doOpt_496 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4)
         (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v4)))
-- Once.Adequacy.MainBuilds.ce-mono-g-doOpt
d_ce'45'mono'45'g'45'doOpt_496 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'mono'45'g'45'doOpt_496 v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_ce'45'mono'45'g'45'doOpt_496 v0 v1 v2 v3 v4 v5
du_ce'45'mono'45'g'45'doOpt_496 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'mono'45'g'45'doOpt_496 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (let v6
             = coe
                 MAlonzo.Code.Once.Compile.d_compileFunM_522
                 (MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                 (coe MAlonzo.Code.Once.IR.C_Heap_8)
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                 (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                 (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                 (MAlonzo.Code.Once.Compile.d_declImps_650
                    (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                 (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) v4
                 (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)) in
       coe
         (case coe v6 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
              -> let v8
                       = MAlonzo.Code.Once.Compile.d_compileEntries_732
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                           (coe v3) in
                 coe
                   (case coe v8 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                                   (coe
                                      MAlonzo.Code.Once.Spec.Name.d_bare_14
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         d_cfunM'45'doOpt_400
                                         (MAlonzo.Code.Once.Parser.d_funType_108 (coe v2)) v0
                                         (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                                         (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                                         (MAlonzo.Code.Once.Compile.d_declImps_650
                                            (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                                         (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) v4
                                         (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)) v7
                                         erased)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_ce'45'doOpt_412 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                         (coe v4))
                                      (coe v3) (coe v9))))
                             erased
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.MainBuilds.ce-poly-p-doOpt
d_ce'45'poly'45'p'45'doOpt_512 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'poly'45'p'45'doOpt_512 v0 v1 v2 v3 v4 v5 ~v6
  = du_ce'45'poly'45'p'45'doOpt_512 v0 v1 v2 v3 v4 v5
du_ce'45'poly'45'p'45'doOpt_512 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'poly'45'p'45'doOpt_512 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v4)
      (coe
         du_ce'45'poly'45'doOpt_528 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Compile.du_checkOK_618
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6328
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1)))
               (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v2))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
                  (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v2)))))
         (coe v5))
-- Once.Adequacy.MainBuilds.ce-poly-doOpt
d_ce'45'poly'45'doOpt_528 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'poly'45'doOpt_528 v0 v1 v2 v3 v4 v5 ~v6
  = du_ce'45'poly'45'doOpt_528 v0 v1 v2 v3 v4 v5
du_ce'45'poly'45'doOpt_528 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'poly'45'doOpt_528 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v4)
      (coe
         du_ce'45'doOpt_412 (coe v0)
         (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v1) (coe v2))
         (coe v3) (coe v5))
-- Once.Adequacy.MainBuilds._.conc
d_conc_610 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_conc_610 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 ~v11
  = du_conc_610 v0 v1 v2 v3 v4 v7 v8 v9 v10
du_conc_610 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conc_610 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      seq (coe v5)
      (coe
         seq (coe v6)
         (coe
            seq (coe v7)
            (coe
               du_ce'45'doOpt_412 (coe v0)
               (coe
                  MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v1)
                  (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
               (coe v3) (coe v8))))
-- Once.Adequacy.MainBuilds.crm-aux-doOpt
d_crm'45'aux'45'doOpt_792 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'aux'45'doOpt_792 v0 ~v1 v2 v3 ~v4
  = du_crm'45'aux'45'doOpt_792 v0 v2 v3
du_crm'45'aux'45'doOpt_792 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'aux'45'doOpt_792 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_ce'45'doOpt_412 (coe v0)
             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v3) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.crm-doOpt
d_crm'45'doOpt_816 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'doOpt_816 v0 v1 v2 ~v3 = du_crm'45'doOpt_816 v0 v1 v2
du_crm'45'doOpt_816 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'doOpt_816 v0 v1 v2
  = coe
      du_crm'45'aux'45'doOpt_792 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_640
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.cfm-built-gated
d_cfm'45'built'45'gated_838 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'gated_838 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du_cfm'45'built'45'gated_838 v1 v4 v6
du_cfm'45'built'45'gated_838 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'gated_838 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Compile.d_printFile_1428 v0
                          (MAlonzo.Code.Once.Compile.d_emit'45'at_1510
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Compile.d_findMain_1286 (coe v2))))
                       erased)
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfm-built-aux
d_cfm'45'built'45'aux_880 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'aux_880 ~v0 v1 v2 ~v3 v4 v5 ~v6
  = du_cfm'45'built'45'aux_880 v1 v2 v4 v5
du_cfm'45'built'45'aux_880 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'aux_880 v0 v1 v2 v3
  = coe
      seq (coe v2)
      (coe
         du_cfm'45'built'45'gated_838 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
            (coe v0) (coe v1))
         (coe v3))
-- Once.Adequacy.MainBuilds.cfm-built-from-crm
d_cfm'45'built'45'from'45'crm_914 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'from'45'crm_914 ~v0 v1 v2 ~v3 v4 ~v5
  = du_cfm'45'built'45'from'45'crm_914 v1 v2 v4
du_cfm'45'built'45'from'45'crm_914 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'from'45'crm_914 v0 v1 v2
  = coe
      du_cfm'45'built'45'aux_880 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_640
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.mtir-aux-inj₂
d_mtir'45'aux'45'inj'8322'_932 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mtir'45'aux'45'inj'8322'_932 v0 ~v1 ~v2
  = du_mtir'45'aux'45'inj'8322'_932 v0
du_mtir'45'aux'45'inj'8322'_932 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mtir'45'aux'45'inj'8322'_932 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.moduleToIR-inj₂
d_moduleToIR'45'inj'8322'_944 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'inj'8322'_944 v0 ~v1 ~v2
  = du_moduleToIR'45'inj'8322'_944 v0
du_moduleToIR'45'inj'8322'_944 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'inj'8322'_944 v0
  = coe
      du_mtir'45'aux'45'inj'8322'_932
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_1060
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.MainBuilds.main⇒built
d_main'8658'built_960 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'8658'built_960 v0 v1 v2 ~v3 ~v4 ~v5
  = du_main'8658'built_960 v0 v1 v2
du_main'8658'built_960 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'8658'built_960 v0 v1 v2
  = coe
      du_cfm'45'built'45'from'45'crm_914 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_crm'45'doOpt_816 (coe v1) (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe du_moduleToIR'45'inj'8322'_944 (coe v2)))))
