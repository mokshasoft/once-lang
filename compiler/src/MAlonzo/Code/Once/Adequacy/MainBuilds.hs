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
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Admissible
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.MainBuilds.cfb-aux-doOpt
d_cfb'45'aux'45'doOpt_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'aux'45'doOpt_30 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 ~v11
  = du_cfb'45'aux'45'doOpt_30 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_cfb'45'aux'45'doOpt_30 ::
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
                          MAlonzo.Code.Once.Optimize.d_optimize_1238
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
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfb-doOpt
d_cfb'45'doOpt_84 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6
du_cfb'45'doOpt_84 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfb'45'doOpt_84 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfb'45'aux'45'doOpt_30
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer)) (coe v1) (coe v2))
      (coe v6) (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe v1) (coe v2))
         (coe v6) (coe v5))
-- Once.Adequacy.MainBuilds.cfun-main-aux-doOpt
d_cfun'45'main'45'aux'45'doOpt_122 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'main'45'aux'45'doOpt_122 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'main'45'aux'45'doOpt_122 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'main'45'aux'45'doOpt_122 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
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
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7
du_cfun'45'aux'45'doOpt_176 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'aux'45'doOpt_176 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v7
      then coe
             du_cfun'45'main'45'aux'45'doOpt_122 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v4) (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v5))
      else coe
             du_cfb'45'doOpt_84 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
-- Once.Adequacy.MainBuilds.cfun-doOpt
d_cfun'45'doOpt_228 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6
du_cfun'45'doOpt_228 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfun'45'doOpt_228 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_cfun'45'aux'45'doOpt_176 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v4)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.MainBuilds.ce-doOpt
d_ce'45'doOpt_256 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'doOpt_256 v0 v1 v2 v3 ~v4 = du_ce'45'doOpt_256 v0 v1 v2 v3
du_ce'45'doOpt_256 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'doOpt_256 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    du_ce'45'fun'45'doOpt_272 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    du_ce'45'poly'45'doOpt_320 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Compile.du_checkOK_372
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                             (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                             (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1)))
                          (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v6))
                          (coe
                             MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v6)))))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-fun-doOpt
d_ce'45'fun'45'doOpt_272 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'fun'45'doOpt_272 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_ce'45'fun'45'doOpt_272 v0 v1 v2 v3 v4
du_ce'45'fun'45'doOpt_272 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'fun'45'doOpt_272 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_ce'45'prim'45'doOpt_288 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
      else coe
             du_ce'45'mono'45'doOpt_304 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_342
                (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
-- Once.Adequacy.MainBuilds.ce-prim-doOpt
d_ce'45'prim'45'doOpt_288 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'prim'45'doOpt_288 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_ce'45'prim'45'doOpt_288 v0 v1 v2 v3 v4
du_ce'45'prim'45'doOpt_288 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'prim'45'doOpt_288 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_conc_402 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v5))
             (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_86 (coe v5))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-mono-doOpt
d_ce'45'mono'45'doOpt_304 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'mono'45'doOpt_304 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_ce'45'mono'45'doOpt_304 v0 v1 v2 v3 v4
du_ce'45'mono'45'doOpt_304 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'mono'45'doOpt_304 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_grd_454 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.ce-poly-doOpt
d_ce'45'poly'45'doOpt_320 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ce'45'poly'45'doOpt_320 v0 v1 v2 v3 v4 v5 ~v6
  = du_ce'45'poly'45'doOpt_320 v0 v1 v2 v3 v4 v5
du_ce'45'poly'45'doOpt_320 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ce'45'poly'45'doOpt_320 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v4)
      (coe
         du_ce'45'doOpt_256 (coe v0)
         (coe MAlonzo.Code.Once.Compile.d_addEntry_432 (coe v1) (coe v2))
         (coe v3) (coe v5))
-- Once.Adequacy.MainBuilds._.conc
d_conc_402 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_conc_402 v0 v1 v2 v3 v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11
  = du_conc_402 v0 v1 v2 v3 v4 v7 v8 v9
du_conc_402 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_conc_402 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> coe
             seq (coe v6)
             (coe
                seq (coe v7)
                (let v9
                       = MAlonzo.Code.Once.Compile.d_compileEntries_448
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                           (coe v3) in
                 coe
                   (case coe v9 of
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                                   (coe
                                      MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.Once.IR.C__'8728'__28
                                      (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                      (coe
                                         MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
                                         (coe (0 :: Integer))
                                         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                         (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                         (coe v4)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                            (coe
                                               MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.d_funName_106
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                            v8))
                                      (coe MAlonzo.Code.Once.IR.C_id_20))
                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_ce'45'doOpt_256 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                         (coe v4))
                                      (coe v3) (coe v10))))
                             erased
                      _ -> MAlonzo.RTE.mazUnreachableError)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds._.grd
d_grd_454 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_grd_454 v0 v1 v2 v3 v4 ~v5 ~v6 v7 ~v8 ~v9
  = du_grd_454 v0 v1 v2 v3 v4 v7
du_grd_454 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_grd_454 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (let v6
             = coe
                 MAlonzo.Code.Once.Compile.du_compileFun'45'aux_176
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                 (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                 (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
                 (coe
                    MAlonzo.Code.Once.Compile.d_declImps_396
                    (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
                 (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                       erased
                       (\ v6 ->
                          coe
                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                          (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                          (coe
                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                             (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                             ("main" :: Data.Text.Text))))) in
       coe
         (case coe v6 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> erased
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
              -> let v8
                       = MAlonzo.Code.Once.Compile.d_compileEntries_448
                           (coe MAlonzo.Code.Once.IR.C_Heap_8)
                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
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
                                   MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                                   (coe
                                      MAlonzo.Code.Once.CanonicalName.d_bare_12
                                      (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         du_cfun'45'doOpt_228 (coe v0)
                                         (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                                         (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
                                         (coe
                                            MAlonzo.Code.Once.Compile.d_declImps_396
                                            (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                         (coe v4)
                                         (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))
                                   (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v2)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_ce'45'doOpt_256 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                                         (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                         (coe v4))
                                      (coe v3) (coe v9))))
                             erased
                      _ -> MAlonzo.RTE.mazUnreachableError)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.Adequacy.MainBuilds.crm-aux-doOpt
d_crm'45'aux'45'doOpt_512 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'aux'45'doOpt_512 v0 ~v1 v2 v3 ~v4
  = du_crm'45'aux'45'doOpt_512 v0 v2 v3
du_crm'45'aux'45'doOpt_512 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'aux'45'doOpt_512 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_ce'45'doOpt_256 (coe v0)
             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_388) (coe v3) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.crm-doOpt
d_crm'45'doOpt_536 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_crm'45'doOpt_536 v0 v1 v2 ~v3 = du_crm'45'doOpt_536 v0 v1 v2
du_crm'45'doOpt_536 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_crm'45'doOpt_536 v0 v1 v2
  = coe
      du_crm'45'aux'45'doOpt_512 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.cfm-built-gated
d_cfm'45'built'45'gated_558 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'gated_558 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7
  = du_cfm'45'built'45'gated_558 v1 v4 v6
du_cfm'45'built'45'gated_558 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'gated_558 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Compile.d_printFile_936 v0
                          (MAlonzo.Code.Once.Compile.d_emit'45'at_1048
                             (coe v0) (coe v2)
                             (coe MAlonzo.Code.Once.Compile.d_findMain_828 (coe v2))))
                       erased)
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.cfm-built-aux
d_cfm'45'built'45'aux_600 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'aux_600 ~v0 v1 v2 ~v3 v4 v5 ~v6
  = du_cfm'45'built'45'aux_600 v1 v2 v4 v5
du_cfm'45'built'45'aux_600 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'aux_600 v0 v1 v2 v3
  = coe
      seq (coe v2)
      (coe
         du_cfm'45'built'45'gated_558 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.Admissible.d_admissibleM'63'_74
            (coe v0) (coe v1))
         (coe v3))
-- Once.Adequacy.MainBuilds.cfm-built-from-crm
d_cfm'45'built'45'from'45'crm_634 ::
  Bool ->
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cfm'45'built'45'from'45'crm_634 ~v0 v1 v2 ~v3 v4 ~v5
  = du_cfm'45'built'45'from'45'crm_634 v1 v2 v4
du_cfm'45'built'45'from'45'crm_634 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cfm'45'built'45'from'45'crm_634 v0 v1 v2
  = coe
      du_cfm'45'built'45'aux_600 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.MainBuilds.mtir-aux-inj₂
d_mtir'45'aux'45'inj'8322'_652 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mtir'45'aux'45'inj'8322'_652 v0 ~v1 ~v2
  = du_mtir'45'aux'45'inj'8322'_652 v0
du_mtir'45'aux'45'inj'8322'_652 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mtir'45'aux'45'inj'8322'_652 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.MainBuilds.moduleToIR-inj₂
d_moduleToIR'45'inj'8322'_664 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToIR'45'inj'8322'_664 v0 ~v1 ~v2
  = du_moduleToIR'45'inj'8322'_664 v0
du_moduleToIR'45'inj'8322'_664 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToIR'45'inj'8322'_664 v0
  = coe
      du_mtir'45'aux'45'inj'8322'_652
      (coe
         MAlonzo.Code.Once.Compile.d_compileResolvedModule_718
         (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v0))
-- Once.Adequacy.MainBuilds.main⇒built
d_main'8658'built_680 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_main'8658'built_680 v0 v1 v2 ~v3 ~v4 ~v5
  = du_main'8658'built_680 v0 v1 v2
du_main'8658'built_680 ::
  MAlonzo.Code.Once.Target.Arch.T_Arch_6 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main'8658'built_680 v0 v1 v2
  = coe
      du_cfm'45'built'45'from'45'crm_634 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_crm'45'doOpt_536 (coe v1) (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe du_moduleToIR'45'inj'8322'_664 (coe v2)))))
