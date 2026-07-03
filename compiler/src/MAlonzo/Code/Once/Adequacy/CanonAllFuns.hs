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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CanonPolyTransport
import qualified MAlonzo.Code.Once.Adequacy.CanonPreserveMutual
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
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
  MAlonzo.Code.Once.Type.T_Type_112 ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8846''45'clash_28 ~v0 ~v1 ~v2 ~v3 = du_'8846''45'clash_28
du_'8846''45'clash_28 :: AgdaAny
du_'8846''45'clash_28 = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.result-extract
d_result'45'extract_34 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_290 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_result'45'extract_34 ~v0 ~v1 v2 = du_result'45'extract_34 v2
du_result'45'extract_34 ::
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_290 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_result'45'extract_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_306 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("Cannot infer type: " :: Data.Text.Text)
                (MAlonzo.Code.Once.TypeCheck.Error.d_renderError_76 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.inferType≡extract
d_inferType'8801'extract_46 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferType'8801'extract_46 = erased
-- Once.Adequacy.CanonAllFuns.inferType→inferElab
d_inferType'8594'inferElab_98 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferType'8594'inferElab_98 v0 v1 v2 ~v3 ~v4
  = du_inferType'8594'inferElab_98 v0 v1 v2
du_inferType'8594'inferElab_98 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferType'8594'inferElab_98 v0 v1 v2
  = coe
      du_go_128
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElab_1500
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
            (coe v0) (coe v1))
         (coe v2))
-- Once.Adequacy.CanonAllFuns._.go
d_go_128 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_290 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 = du_go_128 v7
du_go_128 ::
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_InferElabResult_290 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_128 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased)))
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_306 v1
        -> coe du_'8846''45'clash_28
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.inferElab→inferType
d_inferElab'8594'inferType_178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferElab'8594'inferType_178 = erased
-- Once.Adequacy.CanonAllFuns.inferType-transport
d_inferType'45'transport_202 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inferType'45'transport_202 = erased
-- Once.Adequacy.CanonAllFuns.resolveFunType-transport
d_resolveFunType'45'transport_290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveFunType'45'transport_290 = erased
-- Once.Adequacy.CanonAllFuns.body-transport
d_body'45'transport_356 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_body'45'transport_356 v0 v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_body'45'transport_356 v0 v1 v2 v3 v5 v6 v7 v8
du_body'45'transport_356 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_body'45'transport_356 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v4) in
    coe
      (if coe v8
         then coe
                MAlonzo.Code.Once.Adequacy.CanonPolyTransport.du_polys'45'transport'45''7580'_1102
                (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
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
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))))
                (coe v5) (coe v6) (coe v7)
         else coe
                MAlonzo.Code.Once.Adequacy.CanonPolyTransport.du_polys'45'transport'45''7580'_1102
                (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
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
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))))
                (coe v5) (coe v6)
                (coe
                   MAlonzo.Code.Once.Adequacy.CanonPreserveMutual.du_canon'45'pres'45''7580'_130
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_222
                      (coe v3)
                      (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v1))
                      (coe v2) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4))
                      (coe v5))
                   (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)) (coe v5)
                   (coe v6) (coe v0) (coe v7)))
-- Once.Adequacy.CanonAllFuns.AllFunsTyped-transport
d_AllFunsTyped'45'transport_424 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
d_AllFunsTyped'45'transport_424 v0 v1 v2 v3 ~v4 v5 v6
  = du_AllFunsTyped'45'transport_424 v0 v1 v2 v3 v5 v6
du_AllFunsTyped'45'transport_424 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
du_AllFunsTyped'45'transport_424 v0 v1 v2 v3 v4 v5
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
                       du_body'45'transport_356 (coe v1) (coe v2) (coe v3) (coe v0)
                       (coe v6) (coe v11) (coe v12) (coe v14))
                    (coe
                       du_AllFunsTyped'45'transport_424
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v0)
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v6)) (coe v11))
                       (coe v1) (coe v2) (coe v3) (coe v7) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.AllMainEffUU-transport
d_AllMainEffUU'45'transport_470 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
d_AllMainEffUU'45'transport_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_AllMainEffUU'45'transport_470 v5 v6 v7
du_AllMainEffUU'45'transport_470 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_AllMainEffUU'45'transport_470 v0 v1 v2
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v2)
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                           (coe du_AllMainEffUU'45'transport_470 (coe v4) (coe v12) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonAllFuns.MainExists-transport
d_MainExists'45'transport_518 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
d_MainExists'45'transport_518 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_MainExists'45'transport_518 v5 v6 v7
du_MainExists'45'transport_518 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_MainExists'45'transport_518 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v6 v7 v9 v10
        -> case coe v0 of
             (:) v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_MainExists'45'transport_518 (coe v12) (coe v10) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
