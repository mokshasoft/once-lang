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

module MAlonzo.Code.Once.CompileSrc where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Principal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Concrete
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.SubDecide
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Link
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CompileSrc.Src
d_Src_6 a0 = ()
data T_Src_6
  = C_src_38 Integer MAlonzo.Code.Once.Spec.Context.T_Ctx_8
             MAlonzo.Code.Once.Spec.Context.T_Usage_34
             MAlonzo.Code.Once.IR.T_AllocMode_4 Bool
             MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
-- Once.CompileSrc.Src.n
d_n_24 :: T_Src_6 -> Integer
d_n_24 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.Src.Γ
d_Γ_26 :: T_Src_6 -> MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d_Γ_26 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.Src.Ψ
d_Ψ_28 :: T_Src_6 -> MAlonzo.Code.Once.Spec.Context.T_Usage_34
d_Ψ_28 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.Src.δ
d_δ_30 ::
  T_Src_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_δ_30 = erased
-- Once.CompileSrc.Src.am
d_am_32 :: T_Src_6 -> MAlonzo.Code.Once.IR.T_AllocMode_4
d_am_32 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.Src.opt
d_opt_34 :: T_Src_6 -> Bool
d_opt_34 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.Src.expr
d_expr_36 :: T_Src_6 -> MAlonzo.Code.Once.Surface.Syntax.T_Expr_10
d_expr_36 v0
  = case coe v0 of
      C_src_38 v1 v2 v3 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcIR
d_srcIR_42 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  T_Src_6 -> MAlonzo.Code.Once.IR.T_IR_16
d_srcIR_42 v0 v1
  = case coe v1 of
      C_src_38 v2 v3 v4 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v7)
             (coe
                MAlonzo.Code.Once.Optimize.d_optimize_1848
                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14 (coe v3)))
                (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                   (coe (0 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_934
                   (coe (0 :: Integer)) (coe v2) (coe v3) (coe v4) (coe v0) (coe v8)))
             (coe
                MAlonzo.Code.Once.Surface.Elaborate.du_elaborateFull_934
                (coe (0 :: Integer)) (coe v2) (coe v3) (coe v4) (coe v0) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.mapSrc
d_mapSrc_58 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_mapSrc_58 v0
  = coe
      MAlonzo.Code.Data.Sum.Base.du_map'8322'_94 (d_srcIR_42 (coe v0))
-- Once.CompileSrc.srcBody-aux
d_srcBody'45'aux_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcBody'45'aux_68 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_srcBody'45'aux_68 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_srcBody'45'aux_68 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_srcBody'45'aux_68 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_126 v10 v11 v12 v13
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                C_src_38 v0 v1 v10 v2 v3
                (coe
                   MAlonzo.Code.Once.TypeCheck.Link.du_resolveExpr_500
                   (coe (0 :: Integer)) (coe v8) (coe v5) (coe v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v8))
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v4)))
                   (coe (0 :: Integer)) (coe v11)))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_128 v10
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v7
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text)
                      (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_112 (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcBody
d_srcBody_110 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcBody_110 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_srcBody'45'aux_68 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12) (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_3604
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v2) (coe v3))
         (coe v7) (coe v6))
-- Once.CompileSrc.src-main-aux
d_src'45'main'45'aux_132 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_src'45'main'45'aux_132 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_srcBody_110 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.src-aux
d_src'45'aux_172 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_src'45'aux_172 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             d_src'45'main'45'aux_132 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.Compile.d_validateMain_20 (coe (0 :: Integer))
                (coe v6))
      else coe
             d_srcBody_110 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7)
-- Once.CompileSrc.srcFun
d_srcFun_210 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcFun_210 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_src'45'aux_172 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v5)
         (coe ("main" :: Data.Text.Text)))
-- Once.CompileSrc.srcBodyI-at
d_srcBodyI'45'at_242 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
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
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcBodyI'45'at_242 v0 v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12
                     v13
  = du_srcBodyI'45'at_242 v0 v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13
du_srcBodyI'45'at_242 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
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
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_srcBodyI'45'at_242 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v11 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
        -> if coe v12
             then coe
                    seq (coe v13)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          C_src_38 v0 v1 v2 v4 v5
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Link.du_resolveExpr_500
                             (coe (0 :: Integer)) (coe v10) (coe v7) (coe v8)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v6)))
                             (coe (0 :: Integer)) (coe v3))))
             else coe
                    seq (coe v13)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          ("Type error in " :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                (": its body synthesizes another type than " :: Data.Text.Text)
                                (MAlonzo.Code.Once.Type.d_showType_36
                                   (coe (0 :: Integer)) (coe v10))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcBodyI-aux
d_srcBodyI'45'aux_288 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_82 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcBodyI'45'aux_288 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9 v10
  = du_srcBodyI'45'aux_288 v0 v1 v2 v3 v4 v5 v6 v7 v8 v10
du_srcBodyI'45'aux_288 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_82 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_srcBodyI'45'aux_288 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_98 v10 v11 v12 v13 v14
        -> coe
             du_srcBodyI'45'at_242 (coe v0) (coe v1) (coe v11) (coe v12)
             (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe (0 :: Integer))
                (coe v10) (coe v8))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_100 v10
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v7
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text)
                      (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_112 (coe v10)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcBodyI
d_srcBodyI_332 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcBodyI_332 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_srcBodyI'45'aux_288 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12) (coe v0) (coe v1)
      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_3594
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v2) (coe v3))
         (coe v7))
-- Once.CompileSrc.srcI-main-aux
d_srcI'45'main'45'aux_354 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcI'45'main'45'aux_354 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v8
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> coe
             d_srcBodyI_332 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcI-aux
d_srcI'45'aux_394 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcI'45'aux_394 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = if coe v8
      then coe
             d_srcI'45'main'45'aux_354 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v6) (coe v7)
             (coe
                MAlonzo.Code.Once.Compile.d_validateMain_20 (coe (0 :: Integer))
                (coe v6))
      else coe
             d_srcBodyI_332 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
-- Once.CompileSrc.srcFunI
d_srcFunI_432 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcFunI_432 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      d_srcI'45'aux_394 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v5)
         (coe ("main" :: Data.Text.Text)))
-- Once.CompileSrc.srcM
d_srcM_454 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcM_454 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe d_srcFun_210
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe d_srcFunI_432
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.body-aux-src
d_body'45'aux'45'src_478 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'aux'45'src_478 = erased
-- Once.CompileSrc.body-src
d_body'45'src_532 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'src_532 = erased
-- Once.CompileSrc.main-aux-src
d_main'45'aux'45'src_568 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'aux'45'src_568 = erased
-- Once.CompileSrc.fun-aux-src
d_fun'45'aux'45'src_622 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fun'45'aux'45'src_622 = erased
-- Once.CompileSrc.fun-src
d_fun'45'src_672 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fun'45'src_672 = erased
-- Once.CompileSrc.bodyI-at-src
d_bodyI'45'at'45'src_718 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
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
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bodyI'45'at'45'src_718 = erased
-- Once.CompileSrc.bodyI-aux-src
d_bodyI'45'aux'45'src_778 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bodyI'45'aux'45'src_778 = erased
-- Once.CompileSrc.bodyI-src
d_bodyI'45'src_834 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bodyI'45'src_834 = erased
-- Once.CompileSrc.mainI-aux-src
d_mainI'45'aux'45'src_870 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mainI'45'aux'45'src_870 = erased
-- Once.CompileSrc.funI-aux-src
d_funI'45'aux'45'src_924 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funI'45'aux'45'src_924 = erased
-- Once.CompileSrc.funI-src
d_funI'45'src_974 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_funI'45'src_974 = erased
-- Once.CompileSrc.compileFunM-src
d_compileFunM'45'src_1010 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compileFunM'45'src_1010 = erased
-- Once.CompileSrc.CompiledSrc
d_CompiledSrc_1012 = ()
data T_CompiledSrc_1012
  = C_mkCompiledSrc_1026 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                         MAlonzo.Code.Once.Spec.Type.T_Ty_8 T_Src_6
-- Once.CompileSrc.CompiledSrc.csName
d_csName_1020 ::
  T_CompiledSrc_1012 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_csName_1020 v0
  = case coe v0 of
      C_mkCompiledSrc_1026 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.CompiledSrc.csType
d_csType_1022 ::
  T_CompiledSrc_1012 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_csType_1022 v0
  = case coe v0 of
      C_mkCompiledSrc_1026 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.CompiledSrc.csSrc
d_csSrc_1024 :: T_CompiledSrc_1012 -> T_Src_6
d_csSrc_1024 v0
  = case coe v0 of
      C_mkCompiledSrc_1026 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.toCF
d_toCF_1028 ::
  T_CompiledSrc_1012 -> MAlonzo.Code.Once.Compile.T_CompiledFun_532
d_toCF_1028 v0
  = coe
      MAlonzo.Code.Once.Compile.C_mkCompiledFun_546
      (coe d_csName_1020 (coe v0)) (coe d_csType_1022 (coe v0))
      (coe
         d_srcIR_42 (coe d_csType_1022 (coe v0))
         (coe d_csSrc_1024 (coe v0)))
-- Once.CompileSrc.consCS
d_consCS_1032 ::
  T_CompiledSrc_1012 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_consCS_1032 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.mapCF
d_mapCF_1042 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_mapCF_1042
  = coe
      MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe d_toCF_1028))
-- Once.CompileSrc.srcEntries
d_srcEntries_1044 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcEntries_1044 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_116 v6
               -> coe
                    d_se'45'fun_1048 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_94 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_118 v6
               -> coe
                    d_se'45'poly'45'main_1086 (coe v0) (coe v1) (coe v2) (coe v6)
                    (coe v5)
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54
                       (coe MAlonzo.Code.Once.Parser.d_pfunName_106 (coe v6))
                       (coe ("main" :: Data.Text.Text)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-fun
d_se'45'fun_1048 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'fun_1048 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             d_se'45'prim_1052 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Parser.d_funType_90 (coe v3))
      else coe
             d_se'45'mono_1062 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_602
                (coe MAlonzo.Code.Once.Compile.d_ctop_648 (coe v2))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_654 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funType_90 (coe v3))
                (coe MAlonzo.Code.Once.Parser.d_funBody_92 (coe v3)))
-- Once.CompileSrc.se-prim
d_se'45'prim_1052 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'prim_1052 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             d_se'45'prim'45'conc_1058 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v6))
             (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_200 (coe v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("FFI signature without a type: " :: Data.Text.Text)
                (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-prim-conc
d_se'45'prim'45'conc_1058 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  Maybe AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'prim'45'conc_1058 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    d_srcEntries_1044 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Compile.d_extendSig_716 (coe v2)
                       (coe MAlonzo.Code.Once.Parser.d_funName_88 (coe v3)) (coe v5))
                    (coe v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("FFI signature `" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3))
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
                   (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is not concrete: " :: Data.Text.Text)
                      (MAlonzo.Code.Once.Type.d_showType_36
                         (coe (0 :: Integer)) (coe v5)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-mono
d_se'45'mono_1062 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'mono_1062 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v5
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_se'45'mono'45'p_1068 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v6)
             (coe
                MAlonzo.Code.Once.Compile.d_firstChecking_30 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                   (coe MAlonzo.Code.Once.Compile.d_ctop_648 (coe v2))
                   (coe MAlonzo.Code.Once.Compile.d_cpolys_654 (coe v2)))
                (coe MAlonzo.Code.Once.Parser.d_funBody_92 (coe v3))
                (coe MAlonzo.Code.Once.Principal.du_below_10 (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-mono-p
d_se'45'mono'45'p_1068 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'mono'45'p_1068 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("`" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3))
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
                                        (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3))
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
             d_se'45'mono'45'src_1074 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5)
             (coe
                d_srcM_454 (MAlonzo.Code.Once.Parser.d_funType_90 (coe v3)) v0 v1
                (MAlonzo.Code.Once.Compile.d_ctop_648 (coe v2))
                (MAlonzo.Code.Once.Compile.d_cpolys_654 (coe v2))
                (MAlonzo.Code.Once.Compile.d_declImps_658
                   (coe MAlonzo.Code.Once.Compile.d_ctele_642 (coe v2)))
                (MAlonzo.Code.Once.Parser.d_funName_88 (coe v3)) v5
                (MAlonzo.Code.Once.Parser.d_funBody_92 (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-mono-src
d_se'45'mono'45'src_1074 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'mono'45'src_1074 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v6
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             d_consCS_1032
             (coe
                C_mkCompiledSrc_1026
                (coe
                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe MAlonzo.Code.Once.Parser.d_funName_88 (coe v3)))
                (coe v5) (coe v7))
             (coe
                d_srcEntries_1044 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendScope_708 (coe v2)
                   (coe MAlonzo.Code.Once.Parser.d_funName_88 (coe v3)) (coe v5))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-poly-p
d_se'45'poly'45'p_1078 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'poly'45'p_1078 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("`" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_pfunName_106 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("` is more precise than its schema: the body also checks at "
                       ::
                       Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (MAlonzo.Code.Once.Type.d_showType_36
                            (coe
                               MAlonzo.Code.Once.Type.Instance.d_arityOf_86
                               (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))
                            (coe v6))
                         (". A signature states the body's own type: write the more precise one"
                          ::
                          Data.Text.Text)))))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_se'45'poly_1082 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe
                MAlonzo.Code.Once.Compile.du_checkOK_626
                (coe
                   MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_3604
                   (coe
                      MAlonzo.Code.Once.Type.Instance.d_arityOf_86
                      (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                      (coe
                         MAlonzo.Code.Once.Type.Instance.d_kindsOf_166
                         (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))
                      (coe MAlonzo.Code.Once.Compile.d_ctop_648 (coe v2))
                      (coe MAlonzo.Code.Once.Compile.d_cpolys_654 (coe v2)))
                   (coe MAlonzo.Code.Once.Parser.d_pfunBody_110 (coe v3))
                   (coe
                      MAlonzo.Code.Once.Type.Instance.d_rigidOf_160
                      (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-poly
d_se'45'poly_1082 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'poly_1082 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Type error in " :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (MAlonzo.Code.Once.Parser.d_pfunName_106 (coe v3))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (": " :: Data.Text.Text) v6)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             d_srcEntries_1044 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Compile.d_addEntry_724 (coe v2) (coe v3))
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.se-poly-main
d_se'45'poly'45'main_1086 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_se'45'poly'45'main_1086 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
        -> if coe v6
             then coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          ("main must be usable as Eff Unit Unit (its type below it), but its type is polymorphic or not concrete"
                           ::
                           Data.Text.Text)))
             else coe
                    seq (coe v7)
                    (coe
                       d_se'45'poly'45'p_1078 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Compile.d_firstChecking_30
                          (coe
                             MAlonzo.Code.Once.Type.Instance.d_arityOf_86
                             (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.du_ctxAt_354
                             (coe
                                MAlonzo.Code.Once.Type.Instance.d_kindsOf_166
                                (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3)))
                             (coe MAlonzo.Code.Once.Compile.d_ctop_648 (coe v2))
                             (coe MAlonzo.Code.Once.Compile.d_cpolys_654 (coe v2)))
                          (coe MAlonzo.Code.Once.Parser.d_pfunBody_110 (coe v3))
                          (coe
                             MAlonzo.Code.Once.Principal.du_below_10
                             (coe
                                MAlonzo.Code.Once.Type.Instance.d_rigidOf_160
                                (coe MAlonzo.Code.Once.Parser.d_pfunType_108 (coe v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.consCS-cf
d_consCS'45'cf_1340 ::
  T_CompiledSrc_1012 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consCS'45'cf_1340 = erased
-- Once.CompileSrc.entries-src
d_entries'45'src_1358 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_entries'45'src_1358 = erased
-- Once.CompileSrc.fun-e-src
d_fun'45'e'45'src_1372 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fun'45'e'45'src_1372 = erased
-- Once.CompileSrc.prim-e-src
d_prim'45'e'45'src_1386 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_prim'45'e'45'src_1386 = erased
-- Once.CompileSrc.conc-e-src
d_conc'45'e'45'src_1404 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Type.Concrete.T_IsConcrete_6 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_conc'45'e'45'src_1404 = erased
-- Once.CompileSrc.mono-e-src
d_mono'45'e'45'src_1418 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45'e'45'src_1418 = erased
-- Once.CompileSrc.mono-p-e-src
d_mono'45'p'45'e'45'src_1434 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45'p'45'e'45'src_1434 = erased
-- Once.CompileSrc.mono-ir-e-src
d_mono'45'ir'45'e'45'src_1450 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_78 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45'ir'45'e'45'src_1450 = erased
-- Once.CompileSrc.poly-p-e-src
d_poly'45'p'45'e'45'src_1464 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'p'45'e'45'src_1464 = erased
-- Once.CompileSrc.poly-e-src
d_poly'45'e'45'src_1478 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'e'45'src_1478 = erased
-- Once.CompileSrc.main-e-src
d_main'45'e'45'src_1492 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_630 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_98 ->
  [MAlonzo.Code.Once.Parser.T_Entry_114] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_main'45'e'45'src_1492 = erased
-- Once.CompileSrc.srcModule-aux
d_srcModule'45'aux_1742 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcModule'45'aux_1742 v0 v1 ~v2 v3
  = du_srcModule'45'aux_1742 v0 v1 v3
du_srcModule'45'aux_1742 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_srcModule'45'aux_1742 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             d_srcEntries_1044 (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_646) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.srcModule
d_srcModule_1760 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_srcModule_1760 v0 v1 v2
  = coe
      du_srcModule'45'aux_1742 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Parser.d_extractFunctions_584 (coe v2))
-- Once.CompileSrc.module-aux-src
d_module'45'aux'45'src_1776 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'aux'45'src_1776 = erased
-- Once.CompileSrc.module-src
d_module'45'src_1800 ::
  MAlonzo.Code.Once.IR.T_AllocMode_4 ->
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Resolved_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_module'45'src_1800 = erased
-- Once.CompileSrc.mainOf
d_mainOf_1810 ::
  [T_CompiledSrc_1012] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainOf_1810 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             d_mainOf'45'at_1816 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
                (coe d_csName_1020 (coe v1))
                (coe
                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                   (coe ("main" :: Data.Text.Text))))
             (coe
                MAlonzo.Code.Once.Type.SubDecide.d__'60''58''63'__170
                (coe (0 :: Integer)) (coe d_csType_1022 (coe v1))
                (coe MAlonzo.Code.Once.Compile.du_EffUU_1256))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CompileSrc.mainOf-at
d_mainOf'45'at_1816 ::
  T_CompiledSrc_1012 ->
  [T_CompiledSrc_1012] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mainOf'45'at_1816 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then coe
                    seq (coe v5)
                    (case coe v3 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then case coe v7 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe d_csType_1022 (coe v0)) (coe v8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe seq (coe v7) (coe d_mainOf_1810 (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v5) (coe d_mainOf_1810 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
