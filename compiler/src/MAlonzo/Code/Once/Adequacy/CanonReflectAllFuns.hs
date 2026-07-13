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

module MAlonzo.Code.Once.Adequacy.CanonReflectAllFuns where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.CanonReflectMutual
import qualified MAlonzo.Code.Once.Adequacy.CanonReflectPolyTransport
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CanonReflectAllFuns.inferType-reflect
d_inferType'45'reflect_16 ::
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
d_inferType'45'reflect_16 = erased
-- Once.Adequacy.CanonReflectAllFuns.resolveFunType-reflect
d_resolveFunType'45'reflect_86 ::
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
d_resolveFunType'45'reflect_86 = erased
-- Once.Adequacy.CanonReflectAllFuns.body-reflect
d_body'45'reflect_152 ::
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
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_body'45'reflect_152 v0 v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_body'45'reflect_152 v0 v1 v2 v3 v5 v6 v7 v8
du_body'45'reflect_152 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_body'45'reflect_152 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = MAlonzo.Code.Once.Parser.d_funIsPrimitive_116 (coe v4) in
    coe
      (if coe v8
         then coe
                MAlonzo.Code.Once.Adequacy.CanonReflectPolyTransport.du_polys'45'reflect'45''7580'_202
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
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)) (coe v5)
                (coe v6) (coe v7)
         else coe
                MAlonzo.Code.Once.Adequacy.CanonReflectMutual.du_canon'45'reflects'45''7580'_1150
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                   (coe (0 :: Integer))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                   (coe (0 :: Integer))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v4)) (coe v5))
                      (coe v3))
                   (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v1))
                   (coe v2))
                (coe v5) (coe v6) (coe v0)
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4))
                (coe
                   MAlonzo.Code.Once.Adequacy.CanonReflectPolyTransport.du_polys'45'reflect'45''7580'_202
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
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_294 (coe v0)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v4)))
                   (coe v5) (coe v6) (coe v7)))
-- Once.Adequacy.CanonReflectAllFuns.AllFunsTyped-reflect
d_AllFunsTyped'45'reflect_220 ::
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
d_AllFunsTyped'45'reflect_220 v0 v1 v2 v3 ~v4 v5 v6
  = du_AllFunsTyped'45'reflect_220 v0 v1 v2 v3 v5 v6
du_AllFunsTyped'45'reflect_220 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_120] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124
du_AllFunsTyped'45'reflect_220 v0 v1 v2 v3 v4 v5
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
                       du_body'45'reflect_152 (coe v1) (coe v2) (coe v3) (coe v0) (coe v6)
                       (coe v11) (coe v12) (coe v14))
                    (coe
                       du_AllFunsTyped'45'reflect_220
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v0)
                          (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v6)) (coe v11))
                       (coe v1) (coe v2) (coe v3) (coe v7) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectAllFuns.AllMainEffUU-reflect
d_AllMainEffUU'45'reflect_266 ::
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
d_AllMainEffUU'45'reflect_266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_AllMainEffUU'45'reflect_266 v5 v6 v7
du_AllMainEffUU'45'reflect_266 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_AllMainEffUU'45'reflect_266 v0 v1 v2
  = case coe v0 of
      [] -> coe seq (coe v1) (coe v2)
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                           (coe du_AllMainEffUU'45'reflect_266 (coe v4) (coe v12) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectAllFuns.MainExists-reflect
d_MainExists'45'reflect_314 ::
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
d_MainExists'45'reflect_314 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_MainExists'45'reflect_314 v5 v6 v7
du_MainExists'45'reflect_314 ::
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  MAlonzo.Code.Once.Adequacy.AcceptSound.T_AllFunsTyped_124 ->
  AgdaAny -> AgdaAny
du_MainExists'45'reflect_314 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Adequacy.AcceptSound.C_tcons_144 v8 v9 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13 -> coe v2
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_MainExists'45'reflect_314 (coe v4) (coe v12) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
