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

module MAlonzo.Code.Once.Adequacy.CanonAllFuns where

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
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CanonPolyTransport
import qualified MAlonzo.Code.Once.Adequacy.CanonPreserveMutual
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Principal
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CanonAllFuns.buildPolyCtx-canon
d_buildPolyCtx'45'canon_10 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_buildPolyCtx'45'canon_10 = erased
-- Once.Adequacy.CanonAllFuns.⊎-clash
d_'8846''45'clash_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8846''45'clash_28 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'clash_28
du_'8846''45'clash_28 :: AgdaAny
du_'8846''45'clash_28 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.inj₂-inj
d_inj'8322''45'inj_34 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'8322''45'inj_34 = erased
-- Once.Adequacy.CanonAllFuns.result-extract
d_result'45'extract_40 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_286 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_result'45'extract_40 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v3 v4 v5 v6 v7
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302 v3
        -> coe
             MAlonzo.Code.Once.Compile.d_inferType'45'validate_276 (coe v0)
             (coe v1)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Cannot infer type: " :: Data.Text.Text)
                (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_84 (coe v3)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Principal.d_principalGround_2106
                (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.inferType≡extract
d_inferType'8801'extract_60 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferType'8801'extract_60 = erased
-- Once.Adequacy.CanonAllFuns.itv-inv
d_itv'45'inv_114 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_itv'45'inv_114 v0 v1 ~v2 v3 ~v4 ~v5 = du_itv'45'inv_114 v0 v1 v3
du_itv'45'inv_114 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_itv'45'inv_114 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> let v4
                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
                        (coe v0) (coe v1) (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))))
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v5
                  -> coe du_'8846''45'clash_28
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.itv-intro
d_itv'45'intro_214 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_itv'45'intro_214 = erased
-- Once.Adequacy.CanonAllFuns.InferTypeInv
d_InferTypeInv_236 a0 a1 a2 = ()
data T_InferTypeInv_236
  = C_via'45'elab_252 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                      MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_via'45'oracle_264 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
                        MAlonzo.Code.Once.Surface.Context.T_Usage_60
                        MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer
-- Once.Adequacy.CanonAllFuns.inferType-inv
d_inferType'45'inv_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferTypeInv_236
d_inferType'45'inv_274 v0 v1 v2 ~v3 ~v4
  = du_inferType'45'inv_274 v0 v1 v2
du_inferType'45'inv_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_InferTypeInv_236
du_inferType'45'inv_274 v0 v1 v2
  = coe
      du_go_294 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1302
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
            (coe v0) (coe v1))
         (coe v2))
-- Once.Adequacy.CanonAllFuns._.nctx
d_nctx_290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
d_nctx_290 v0 v1 ~v2 ~v3 ~v4 = du_nctx_290 v0 v1
du_nctx_290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
du_nctx_290 v0 v1
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
      (coe v0) (coe v1)
-- Once.Adequacy.CanonAllFuns._.go
d_go_294 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_286 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferTypeInv_236
d_go_294 v0 v1 v2 ~v3 ~v4 v5 ~v6 = du_go_294 v0 v1 v2 v5
du_go_294 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_286 ->
  T_InferTypeInv_236
du_go_294 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v4 v5 v6 v7 v8
        -> coe du_goS_314 (coe v5) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_302 v4
        -> coe
             du_go2_332 (coe v4)
             (coe
                du_itv'45'inv_114 (coe du_nctx_290 (coe v0) (coe v1)) (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Principal.d_principalGround_2106
                   (coe du_nctx_290 (coe v0) (coe v1)) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns._._.re
d_re_312 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_re_312 = erased
-- Once.Adequacy.CanonAllFuns._._.goS
d_goS_314 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_InferTypeInv_236
d_goS_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11
  = du_goS_314 v6 v7 v8 v9
du_goS_314 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> T_InferTypeInv_236
du_goS_314 v0 v1 v2 v3 = coe C_via'45'elab_252 v0 v1 v2 v3
-- Once.Adequacy.CanonAllFuns._._.go2
d_go2_332 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_InferTypeInv_236
d_go2_332 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_go2_332 v5 v7
du_go2_332 ::
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_InferTypeInv_236
du_go2_332 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                    -> coe C_via'45'oracle_264 v0 v4 v6 v8 v10
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.inferElab→inferType
d_inferElab'8594'inferType_362 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'8594'inferType_362 = erased
-- Once.Adequacy.CanonAllFuns._.polysB
d_polysB_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polysB_390 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_polysB_390 v1
du_polysB_390 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_polysB_390 v0
  = coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v0)
-- Once.Adequacy.CanonAllFuns._.polysC
d_polysC_392 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polysC_392 ~v0 v1 v2 ~v3 ~v4 ~v5 = du_polysC_392 v1 v2
du_polysC_392 ::
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_polysC_392 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.CanonPolyTransport.d_canonPolysCtx_6
      (coe v1) (coe du_polysB_390 (coe v0))
-- Once.Adequacy.CanonAllFuns._.nctxS
d_nctxS_394 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
d_nctxS_394 v0 v1 ~v2 ~v3 ~v4 ~v5 = du_nctxS_394 v0 v1
du_nctxS_394 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
du_nctxS_394 v0 v1
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
      (coe v0) (coe du_polysB_390 (coe v1))
-- Once.Adequacy.CanonAllFuns._.nctxC
d_nctxC_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
d_nctxC_396 v0 v1 v2 ~v3 ~v4 ~v5 = du_nctxC_396 v0 v1 v2
du_nctxC_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
du_nctxC_396 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
      (coe v0) (coe du_polysC_392 (coe v1) (coe v2))
-- Once.Adequacy.CanonAllFuns._.wf
d_wf_398 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_wf_398 = erased
-- Once.Adequacy.CanonAllFuns._.clash
d_clash_414 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_clash_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14
  = du_clash_414
du_clash_414 :: AgdaAny
du_clash_414 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns._.oracle-transport-prim
d_oracle'45'transport'45'prim_438 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_oracle'45'transport'45'prim_438 = erased
-- Once.Adequacy.CanonAllFuns._.oracle-transport-user
d_oracle'45'transport'45'user_490 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_oracle'45'transport'45'user_490 = erased
-- Once.Adequacy.CanonAllFuns.inferType-transport
d_inferType'45'transport_544 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferType'45'transport_544 = erased
-- Once.Adequacy.CanonAllFuns.resolveFunType-transport
d_resolveFunType'45'transport_656 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveFunType'45'transport_656 = erased
-- Once.Adequacy.CanonAllFuns.body-transport
d_body'45'transport_722 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_body'45'transport_722 v0 v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_body'45'transport_722 v0 v1 v2 v3 v5 v6 v7 v8
du_body'45'transport_722 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_body'45'transport_722 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v4) in
    coe
      (if coe v8
         then coe
                MAlonzo.Code.Once.Adequacy.CanonPolyTransport.du_polys'45'transport'45''7580'_1788
                (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v5))
                   (coe v3))
                (coe v2)
                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v1))
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v8)
                   (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))))
                (coe v5) (coe v6) (coe v7)
         else coe
                MAlonzo.Code.Once.Adequacy.CanonPolyTransport.du_polys'45'transport'45''7580'_1788
                (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v5))
                   (coe v3))
                (coe v2)
                (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v1))
                (coe
                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v8)
                   (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))))
                (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Adequacy.CanonPreserveMutual.du_canon'45'pres'45''7580'_116
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                      (coe v3)
                      (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v1))
                      (coe v2) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4))
                      (coe v5))
                   (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)) (coe v5)
                   (coe v6) (coe v0) (coe v7)))
-- Once.Adequacy.CanonAllFuns.AllFunsTyped-transport
d_AllFunsTyped'45'transport_790 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
d_AllFunsTyped'45'transport_790 v0 v1 v2 v3 ~v4 v5 v6
  = du_AllFunsTyped'45'transport_790 v0 v1 v2 v3 v5 v6
du_AllFunsTyped'45'transport_790 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
du_AllFunsTyped'45'transport_790 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      []
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Once.Adequacy.AcceptSound.C_tnil_132)
      (:) v6 v7
        -> case coe v5 of
             MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v11 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v11 v12
                    (coe
                       du_body'45'transport_722 (coe v1) (coe v2) (coe v3) (coe v0)
                       (coe v6) (coe v11) (coe v12) (coe v14))
                    (coe
                       du_AllFunsTyped'45'transport_790
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v0)
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v6)) (coe v11))
                       (coe v1) (coe v2) (coe v3) (coe v7) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.AllMainEffUU-transport
d_AllMainEffUU'45'transport_836 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
d_AllMainEffUU'45'transport_836 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_AllMainEffUU'45'transport_836 v5 v6 v7
du_AllMainEffUU'45'transport_836 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_AllMainEffUU'45'transport_836 v0 v1 v2
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v2)
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                           (coe du_AllMainEffUU'45'transport_836 (coe v4) (coe v12) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.MainExists-transport
d_MainExists'45'transport_884 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
d_MainExists'45'transport_884 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_MainExists'45'transport_884 v5 v6 v7
du_MainExists'45'transport_884 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_MainExists'45'transport_884 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v6 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_MainExists'45'transport_884 (coe v12) (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
