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

module MAlonzo.Code.Once.Adequacy.AcceptSound where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.MainBuilds
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Honest
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.Soundness

-- Once.Adequacy.AcceptSound.compileFunBody-aux-success
d_compileFunBody'45'aux'45'success_36 ::
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
d_compileFunBody'45'aux'45'success_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 v9 ~v10 ~v11
  = du_compileFunBody'45'aux'45'success_36 v9
du_compileFunBody'45'aux'45'success_36 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'aux'45'success_36 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.compileFunBody-sound
d_compileFunBody'45'sound_96 ::
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
d_compileFunBody'45'sound_96 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'sound_96 v1 v2 v5 v6
du_compileFunBody'45'sound_96 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'sound_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_compileFunBody'45'aux'45'success_36
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6158
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                  (coe v0) (coe v1))
               (coe v3) (coe v2))))
      (coe
         MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2502
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe v0) (coe v1))
         (coe v3) (coe v2))
-- Once.Adequacy.AcceptSound.compileFun-main-aux-sound
d_compileFun'45'main'45'aux'45'sound_146 ::
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
d_compileFun'45'main'45'aux'45'sound_146 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7
                                         ~v8 ~v9
  = du_compileFun'45'main'45'aux'45'sound_146 v1 v2 v5 v6 v7
du_compileFun'45'main'45'aux'45'sound_146 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'sound_146 v0 v1 v2 v3 v4
  = coe
      seq (coe v4)
      (coe
         du_compileFunBody'45'sound_96 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.AcceptSound.compileFun-aux-sound
d_compileFun'45'aux'45'sound_200 ::
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
d_compileFun'45'aux'45'sound_200 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'sound_200 v1 v2 v5 v6 v7
du_compileFun'45'aux'45'sound_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'sound_200 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_compileFun'45'main'45'aux'45'sound_146 (coe v0) (coe v1)
             (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v2))
      else coe
             du_compileFunBody'45'sound_96 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.AcceptSound.compileFun-sound
d_compileFun'45'sound_252 ::
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
d_compileFun'45'sound_252 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'sound_252 v1 v2 v4 v5 v6
du_compileFun'45'sound_252 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'sound_252 v0 v1 v2 v3 v4
  = coe
      du_compileFun'45'aux'45'sound_200 (coe v0) (coe v1) (coe v3)
      (coe v4)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.AcceptSound.scopeOf
d_scopeOf_270 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Spec.Module.T_Scope_6
d_scopeOf_270 v0
  = coe
      MAlonzo.Code.Once.Spec.Module.C_scope_16
      (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_390
         (MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0)))
-- Once.Adequacy.AcceptSound.usage0
d_usage0_276 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_usage0_276 = erased
-- Once.Adequacy.AcceptSound.consCF-inj
d_consCF'45'inj_286 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_232 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consCF'45'inj_286 ~v0 v1 ~v2 ~v3 = du_consCF'45'inj_286 v1
du_consCF'45'inj_286 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consCF'45'inj_286 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.checkOK-sound
d_checkOK'45'sound_300 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkOK'45'sound_300 ~v0 ~v1 ~v2 v3 ~v4
  = du_checkOK'45'sound_300 v3
du_checkOK'45'sound_300 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkOK'45'sound_300 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v3 v4 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-sound
d_ce'45'sound_314 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_ce'45'sound_314 v0 v1 v2 v3 ~v4 = du_ce'45'sound_314 v0 v1 v2 v3
du_ce'45'sound_314 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_ce'45'sound_314 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe MAlonzo.Code.Once.Spec.Module.C_'91''93'_42
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    du_ce'45'fun'45'sound_328 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    du_ce'45'poly'45'sound_368 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-fun-sound
d_ce'45'fun'45'sound_328 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_ce'45'fun'45'sound_328 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7
  = du_ce'45'fun'45'sound_328 v0 v1 v2 v3 v4
du_ce'45'fun'45'sound_328 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool -> MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_ce'45'fun'45'sound_328 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_ce'45'prim'45'sound_342 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
      else coe
             du_ce'45'mono'45'sound_356 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_342
                (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
-- Once.Adequacy.AcceptSound.ce-prim-sound
d_ce'45'prim'45'sound_342 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_ce'45'prim'45'sound_342 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_ce'45'prim'45'sound_342 v0 v1 v2 v3 v5
du_ce'45'prim'45'sound_342 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_ce'45'prim'45'sound_342 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             du_conc_460 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v5))
             (coe MAlonzo.Code.Once.Type.Honest.d_honest'63'_86 (coe v5))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-mono-sound
d_ce'45'mono'45'sound_356 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_ce'45'mono'45'sound_356 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_ce'45'mono'45'sound_356 v0 v1 v2 v3 v5
du_ce'45'mono'45'sound_356 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_ce'45'mono'45'sound_356 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_grd_506 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_838 (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-poly-sound
d_ce'45'poly'45'sound_368 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_ce'45'poly'45'sound_368 v0 v1 v2 v3 v4 ~v5
  = du_ce'45'poly'45'sound_368 v0 v1 v2 v3 v4
du_ce'45'poly'45'sound_368 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_ce'45'poly'45'sound_368 v0 v1 v2 v3 v4
  = coe
      du_step_552 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6158
         (coe du_ctx_546 (coe v1))
         (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v2))
         (coe
            MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124
            (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v2))))
      (coe v4)
-- Once.Adequacy.AcceptSound._.conc
d_conc_460 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_conc_460 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 v13 ~v14
           ~v15 ~v16
  = du_conc_460 v0 v1 v2 v3 v5 v9 v11 v13
du_conc_460 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_conc_460 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> coe
                           MAlonzo.Code.Once.Spec.Module.C_ffi_52 v4 v8 v9 v10
                           (coe
                              du_ce'45'sound_314 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    du_consCF'45'inj_286
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_compileEntries_448
                                       (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                          (coe v4))
                                       (coe v3)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._.grd
d_grd_506 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_grd_506 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_grd_506 v0 v1 v2 v3 v5 v9
du_grd_506 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_grd_506 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_step_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe
                MAlonzo.Code.Once.Compile.du_compileFun_214 (coe v0)
                (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
                (coe
                   MAlonzo.Code.Once.Compile.d_declImps_396
                   (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._._.step
d_step_520 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_step_520 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 v12 ~v13
           ~v14 ~v15
  = du_step_520 v0 v1 v2 v3 v5 v9 v12
du_step_520 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_step_520 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         MAlonzo.Code.Once.Spec.Module.C_mono_64 v4
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_compileFun'45'sound_252
               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))
         v5
         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               du_compileFun'45'sound_252
               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4)
               (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))
         (coe
            du_ce'45'sound_314 (coe v0)
            (coe
               MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
            (coe v3)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe
                  du_consCF'45'inj_286
                  (coe
                     MAlonzo.Code.Once.Compile.d_compileEntries_448
                     (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0)
                     (coe
                        MAlonzo.Code.Once.Compile.d_extendScope_424 (coe v1)
                        (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                     (coe v3))))))
-- Once.Adequacy.AcceptSound._.ctx
d_ctx_546 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
d_ctx_546 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_ctx_546 v1
du_ctx_546 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378
du_ctx_546 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
      (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0))
-- Once.Adequacy.AcceptSound._.step
d_step_552 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_step_552 v0 v1 v2 v3 ~v4 ~v5 v6 ~v7 v8 ~v9
  = du_step_552 v0 v1 v2 v3 v6 v8
du_step_552 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_step_552 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v8 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Spec.Module.C_poly_74 v8 v7
                    (coe
                       du_ce'45'sound_314 (coe v0)
                       (coe MAlonzo.Code.Once.Compile.d_addEntry_432 (coe v1) (coe v2))
                       (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.crm-aux-sound
d_crm'45'aux'45'sound_572 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'aux'45'sound_572 v0 ~v1 v2 v3 ~v4
  = du_crm'45'aux'45'sound_572 v0 v2 v3
du_crm'45'aux'45'sound_572 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] -> AgdaAny
du_crm'45'aux'45'sound_572 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_ce'45'sound_314 (coe v0)
             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_388) (coe v3) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.crm-sound
d_crm'45'sound_594 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'sound_594 v0 v1 v2 ~v3 = du_crm'45'sound_594 v0 v1 v2
du_crm'45'sound_594 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_232] -> AgdaAny
du_crm'45'sound_594 v0 v1 v2
  = coe
      du_crm'45'aux'45'sound_572 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_572
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.AcceptSound.moduleToIR-typed
d_moduleToIR'45'typed_606 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'typed_606 v0 ~v1 ~v2
  = du_moduleToIR'45'typed_606 v0
du_moduleToIR'45'typed_606 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny
du_moduleToIR'45'typed_606 v0
  = coe
      du_crm'45'sound_594 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Adequacy.MainBuilds.du_moduleToIR'45'inj'8322'_662
            (coe v0)))
