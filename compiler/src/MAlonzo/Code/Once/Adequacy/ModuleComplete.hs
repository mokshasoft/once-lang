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

module MAlonzo.Code.Once.Adequacy.ModuleComplete where

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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.MainIRForm
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ModuleComplete.cong₃
d_cong'8323'_28 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8323'_28 = erased
-- Once.Adequacy.ModuleComplete.compileFunBody-complete
d_compileFunBody'45'complete_48 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6
du_compileFunBody'45'complete_48 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'complete_48 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         du_succ_78 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe v0) (coe v1))
            (coe v5) (coe v4)))
-- Once.Adequacy.ModuleComplete._.succ
d_succ_78 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_succ_78 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_succ_78 v0 v1 v2 v3 v4 v5 v7
du_succ_78 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_succ_78 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             seq (coe v7)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                   (coe
                      MAlonzo.Code.Once.Optimize.d_optimize_1248
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                            (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)))
                      (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                      (coe
                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                         (coe (0 :: Integer))
                         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                         (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                         (coe
                            MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                            (coe v4) (coe v1) (coe v2)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                            (coe (0 :: Integer))
                            (coe
                               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                               (coe
                                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                  (coe (0 :: Integer))
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                  (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
                                  (coe v1)
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
                               (coe v5) (coe v4)
                               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v8)))))
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                      (coe (0 :: Integer))
                      (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                      (coe
                         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                         (coe v4) (coe v1) (coe v2)
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                         (coe (0 :: Integer))
                         (coe
                            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                            (coe
                               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                               (coe (0 :: Integer))
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                               (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
                               (coe v1)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
                            (coe v5) (coe v4)
                            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v8)))))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.compileFun-complete
d_compileFun'45'complete_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6
du_compileFun'45'complete_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'complete_96 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v3))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          du_main'45'step_160 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                          (coe v6)
                          (coe
                             MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v4)
                             (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_168)))
                else coe
                       seq (coe v9)
                       (coe
                          du_compileFunBody'45'complete_48 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v5) (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._.main-step
d_main'45'step_160 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'step_160 v0 v1 v2 v3 v4 v5 ~v6 ~v7 v8 ~v9
  = du_main'45'step_160 v0 v1 v2 v3 v4 v5 v8
du_main'45'step_160 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'step_160 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       du_compileFunBody'45'complete_48 (coe v0) (coe v1) (coe v2)
                       (coe ("main" :: Data.Text.Text)) (coe v3) (coe v4) (coe v5))
             else coe
                    seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.compileFunBodyI-complete
d_compileFunBodyI'45'complete_182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBodyI'45'complete_182 v0 v1 v2 v3 ~v4 v5 v6 ~v7
  = du_compileFunBodyI'45'complete_182 v0 v1 v2 v3 v5 v6
du_compileFunBodyI'45'complete_182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBodyI'45'complete_182 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (coe
         du_succ_226 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe v0) (coe v1))
            (coe v4)))
-- Once.Adequacy.ModuleComplete._.at
d_at_208 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_208 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_at_208 v0 v1 v2 v3 v4 v5 v7 v8
du_at_208 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_208 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe
                             MAlonzo.Code.Once.Optimize.d_optimize_1248
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'10214'_'10215''7580'_38
                                   (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)))
                             (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v4))
                             (coe
                                MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                                   (coe v4) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                         (coe v4))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                                   (coe (0 :: Integer))
                                   (coe
                                      MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                      (coe
                                         MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                         (coe (0 :: Integer))
                                         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                         (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                                            (coe v0))
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                                            (coe v0)))
                                      (coe v5) (coe v4)
                                      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
                                      (coe v6)))))
                          (coe
                             MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_1050
                             (coe (0 :: Integer))
                             (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                             (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v4)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
                                (coe v4) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0)))
                                (coe (0 :: Integer))
                                (coe
                                   MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
                                   (coe
                                      MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                      (coe (0 :: Integer))
                                      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                      (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v0))
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v0)))
                                   (coe v5) (coe v4)
                                   (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v6)))))
                       erased)
             else coe
                    seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.succ
d_succ_226 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_succ_226 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8 ~v9 ~v10 ~v11
  = du_succ_226 v0 v1 v2 v3 v5 v7
du_succ_226 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_succ_226 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v8 v9 v10 v11 v12
               -> coe
                    du_at_208 (coe v0) (coe v1) (coe v2) (coe v3) (coe v8) (coe v4)
                    (coe v7)
                    (coe
                       MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v8)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.compileFunI-complete
d_compileFunI'45'complete_246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunI'45'complete_246 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFunI'45'complete_246 v0 v1 v2 v3 v4 v5 v6
du_compileFunI'45'complete_246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunI'45'complete_246 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v3))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                 (coe ("main" :: Data.Text.Text))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (coe
                          du_main'45'step_310 (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
                          (coe
                             MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v4)
                             (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_168)))
                else coe
                       seq (coe v9)
                       (coe
                          du_compileFunBodyI'45'complete_182 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v5) (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete._.main-step
d_main'45'step_310 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'45'step_310 v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8 ~v9
  = du_main'45'step_310 v0 v1 v2 v4 v5 v8
du_main'45'step_310 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'45'step_310 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       du_compileFunBodyI'45'complete_182 (coe v0) (coe v1) (coe v2)
                       (coe ("main" :: Data.Text.Text)) (coe v3) (coe v4))
             else coe
                    seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.compileFunM-complete
d_compileFunM'45'complete_334 ::
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunM'45'complete_334 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
                coe du_compileFun'45'complete_96 v2 v3 v4 v5 v6 v7 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
                coe du_compileFunI'45'complete_246 v1 v2 v3 v4 v5 v6 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.scopeOf
d_scopeOf_336 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6
d_scopeOf_336
  = coe MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_494
-- Once.Adequacy.ModuleComplete.checkOK-complete
d_checkOK'45'complete_354 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkOK'45'complete_354 = erased
-- Once.Adequacy.ModuleComplete.ce-complete
d_ce'45'complete_364 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'complete_364 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_74
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      MAlonzo.Code.Once.Lang.Module.C_ffi_84 v6 v10 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'complete_364
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v16)) (coe v6))
                                 (coe v15) (coe v13) (coe v3)))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_96 v6 v8 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v17
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe
                                        MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                                        (coe
                                           MAlonzo.Code.Once.Spec.Name.d_bare_14
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)))
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                           (coe
                                              d_compileFunM'45'complete_334
                                              (MAlonzo.Code.Once.Parser.d_funType_108 (coe v17))
                                              (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
                                              (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
                                              (MAlonzo.Code.Once.Compile.d_declImps_650
                                                 (coe
                                                    MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
                                              (MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) v6
                                              (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v17)) v8
                                              v18 v13)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_ce'45'complete_364
                                           (coe
                                              MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17))
                                              (coe v6))
                                           (coe v16) (coe v14) (coe v19))))
                                  erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_106 v7 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'complete_364
                                 (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0) (coe v13))
                                 (coe v12) (coe v10) (coe v3)))
                           erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.FindResult
d_FindResult_454 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] -> ()
d_FindResult_454 = erased
-- Once.Adequacy.ModuleComplete.ce-find-complete
d_ce'45'find'45'complete_470 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'find'45'complete_470 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_ffi_84 v7 v11 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'find'45'complete_470
                                 (coe
                                    MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                                    (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) (coe v7))
                                 (coe v16) (coe v14) (coe v3) (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ce'45'find'45'complete_470
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v17))
                                          (coe v7))
                                       (coe v16) (coe v14) (coe v3) (coe v4))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ce'45'find'45'complete_470
                                             (coe
                                                MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                                                (coe
                                                   MAlonzo.Code.Once.Parser.d_funName_106 (coe v17))
                                                (coe v7))
                                             (coe v16) (coe v14) (coe v3) (coe v4)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_96 v7 v9 v13 v14 v15
        -> case coe v1 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v18
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                             -> coe
                                  du_step_638 (coe v0) (coe v18) (coe v7) (coe v17) (coe v9)
                                  (coe v14) (coe v15) (coe v19) (coe v20) (coe v4)
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                     (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v18))
                                     (coe ("main" :: Data.Text.Text)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_106 v8 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 d_ce'45'find'45'complete_470
                                 (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0) (coe v14))
                                 (coe v13) (coe v11) (coe v3) (coe v4)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       d_ce'45'find'45'complete_470
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0)
                                          (coe v14))
                                       (coe v13) (coe v11) (coe v3) (coe v4))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_ce'45'find'45'complete_470
                                             (coe
                                                MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0)
                                                (coe v14))
                                             (coe v13) (coe v11) (coe v3) (coe v4)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.cfc
d_cfc_570 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfc_570 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_cfc_570 v0 v1 v2 v4 v9 v11
du_cfc_570 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfc_570 v0 v1 v2 v3 v4 v5
  = coe
      d_compileFunM'45'complete_334
      (MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
      (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
      (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
      (MAlonzo.Code.Once.Compile.d_declImps_650
         (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
      (MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) v2
      (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) v3 v5 v4
-- Once.Adequacy.ModuleComplete._.irFun
d_irFun_572 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16
d_irFun_572 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_irFun_572 v0 v1 v2 v4 v9 v11
du_irFun_572 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.IR.T_IR_16
du_irFun_572 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         du_cfc_570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Adequacy.ModuleComplete._.chain
d_chain_576 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chain_576 = erased
-- Once.Adequacy.ModuleComplete._.cf0
d_cf0_580 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_524
d_cf0_580 v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 ~v13
  = du_cf0_580 v0 v1 v2 v4 v9 v11
du_cf0_580 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  MAlonzo.Code.Once.Compile.T_CompiledFun_524
du_cf0_580 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
      (coe
         MAlonzo.Code.Once.Spec.Name.d_bare_14
         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)))
      (coe v2)
      (coe
         du_irFun_572 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Adequacy.ModuleComplete._.here
d_here_586 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_here_586 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16
  = du_here_586 v2
du_here_586 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_here_586 v0 = coe du_found_630 (coe v0)
-- Once.Adequacy.ModuleComplete._._.foundD
d_foundD_606 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_foundD_606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19 ~v20
  = du_foundD_606 v19
du_foundD_606 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_foundD_606 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then case coe v2 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Compile.du_mainEntry_1258 (coe v3)) erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v2) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._._.found
d_found_630 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_found_630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 ~v17 v18 ~v19 ~v20 ~v21
  = du_found_630 v18
du_found_630 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_found_630 v0
  = coe
      du_foundD_606
      (coe
         MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_168))
-- Once.Adequacy.ModuleComplete._.step
d_step_638 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_638 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11 v12 ~v13 v14
           v15
  = du_step_638 v0 v1 v2 v3 v4 v9 v10 v11 v12 v14 v15
du_step_638 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_638 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
        -> coe
             seq (coe v11)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      du_cf0_580 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5) (coe v7))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         d_ce'45'complete_364
                         (coe
                            MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                         (coe v3) (coe v6) (coe v8))))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe du_here_586 (coe v2)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                         (coe du_here_586 (coe v2))))))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
        -> case coe v10 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
               -> if coe v12
                    then coe
                           seq (coe v13)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    du_cf0_580 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe v7))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ce'45'complete_364
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                          (coe v2))
                                       (coe v3) (coe v6) (coe v8))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_here_586 (coe v2)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe du_here_586 (coe v2))))))
                    else coe
                           seq (coe v13)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    du_cf0_580 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
                                    (coe v7))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_ce'45'find'45'complete_470
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                          (coe v2))
                                       (coe v3) (coe v6) (coe v8) (coe v11))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_ce'45'find'45'complete_470
                                          (coe
                                             MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                                             (coe v2))
                                          (coe v3) (coe v6) (coe v8) (coe v11))))
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.moduleToIR-complete
d_moduleToIR'45'complete_684 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'complete_684 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_542
              (coe
                 MAlonzo.Code.Once.Parser.d_thenExtract_626
                 (coe
                    MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                    (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                 (coe
                    MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                    (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Parser.d_sigsFirst_622
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0)))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> let v5
                    = d_ce'45'find'45'complete_470
                        (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v4) (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe
                                 seq (coe v9)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ModuleComplete.ce-mains
d_ce'45'mains_732 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_ce'45'mains_732 v0 v1 v2 ~v3 ~v4 = du_ce'45'mains_732 v0 v1 v2
du_ce'45'mains_732 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 -> AgdaAny
du_ce'45'mains_732 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_74
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Module.C_ffi_84 v5 v9 v10 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v15
                      -> coe
                           du_ce'45'mains_732
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v15)) (coe v5))
                           (coe v14) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_96 v5 v7 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v16
                      -> coe
                           du_go_812 (coe v0) (coe v16) (coe v5) (coe v15) (coe v13)
                           (coe
                              MAlonzo.Code.Once.Compile.d_compileFunM_522
                              (MAlonzo.Code.Once.Parser.d_funType_108 (coe v16))
                              (coe MAlonzo.Code.Once.IR.C_Heap_8)
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
                              (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
                              (MAlonzo.Code.Once.Compile.d_declImps_650
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
                              (MAlonzo.Code.Once.Parser.d_funName_106 (coe v16)) v5
                              (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v16)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_106 v6 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v12
                      -> coe
                           du_ce'45'mains_732
                           (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0) (coe v12))
                           (coe v11) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.eq′
d_eq'8242'_806 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'8242'_806 = erased
-- Once.Adequacy.ModuleComplete._.go
d_go_812 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_812 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13 ~v14
  = du_go_812 v0 v1 v2 v3 v10 v13
du_go_812 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_812 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Once.Adequacy.MainIRForm.d_compileFunM'45'main'45'sub_144
                     (MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
                     (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
                     (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
                     (MAlonzo.Code.Once.Compile.d_declImps_650
                        (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
                     v2 (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) v6 erased))
             (coe
                du_ce'45'mains_732
                (coe
                   MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.ce-mainexists
d_ce'45'mainexists_838 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_ce'45'mainexists_838 v0 v1 v2 ~v3 v4 ~v5 ~v6
  = du_ce'45'mainexists_838 v0 v1 v2 v4
du_ce'45'mainexists_838 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_ce'45'mainexists_838 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_74 -> erased
      MAlonzo.Code.Once.Lang.Module.C_ffi_84 v6 v10 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v16
                      -> coe
                           du_ce'45'mainexists_838
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v16)) (coe v6))
                           (coe v15) (coe v13) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_mono_96 v6 v8 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v17
                      -> coe
                           du_go_938 (coe v0) (coe v17) (coe v6) (coe v16) (coe v14) (coe v3)
                           (coe
                              MAlonzo.Code.Once.Compile.d_compileFunM_522
                              (MAlonzo.Code.Once.Parser.d_funType_108 (coe v17))
                              (coe MAlonzo.Code.Once.IR.C_Heap_8)
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
                              (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
                              (MAlonzo.Code.Once.Compile.d_declImps_650
                                 (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
                              (MAlonzo.Code.Once.Parser.d_funName_106 (coe v17)) v6
                              (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v17)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_106 v7 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v13
                      -> coe
                           du_ce'45'mainexists_838
                           (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v0) (coe v13))
                           (coe v12) (coe v10) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._.eq′
d_eq'8242'_932 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'8242'_932 = erased
-- Once.Adequacy.ModuleComplete._.go
d_go_938 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_938 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 ~v13 ~v14
         v15 ~v16
  = du_go_938 v0 v1 v2 v3 v10 v12 v15
du_go_938 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_938 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_decide_952 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v7)
             (coe
                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1))
                (coe ("main" :: Data.Text.Text)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete._._.decide
d_decide_952 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_decide_952 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 v12 ~v13
             ~v14 v15 ~v16 v17
  = du_decide_952 v0 v1 v2 v3 v10 v12 v15 v17
du_decide_952 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_decide_952 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then case coe v9 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Adequacy.MainIRForm.d_compileFunM'45'main'45'sub_144
                                 (MAlonzo.Code.Once.Parser.d_funType_108 (coe v1))
                                 (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
                                 (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
                                 (MAlonzo.Code.Once.Compile.d_declImps_650
                                    (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
                                 v2 (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v1)) v6 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          du_ce'45'mainexists_838
                          (coe
                             MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v0)
                             (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v1)) (coe v2))
                          (coe v3) (coe v4) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ModuleComplete.moduleToIR-sound
d_moduleToIR'45'sound_984 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'sound_984 v0 v1 v2 ~v3
  = du_moduleToIR'45'sound_984 v0 v1 v2
du_moduleToIR'45'sound_984 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  AgdaAny -> MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_moduleToIR'45'sound_984 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.d_guardDistinct_542
              (coe
                 MAlonzo.Code.Once.Parser.d_thenExtract_626
                 (coe
                    MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                    (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                 (coe
                    MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                    (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Parser.d_sigsFirst_622
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0)))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
           -> let v5
                    = MAlonzo.Code.Once.Compile.d_compileEntries_732
                        (coe MAlonzo.Code.Once.IR.C_Heap_8)
                        (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                        (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             du_ce'45'mains_732
                             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v4)
                             (coe v1))
                          (coe
                             du_ce'45'mainexists_838
                             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v4) (coe v1)
                             (coe v2))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
