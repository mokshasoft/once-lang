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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.TypeCheck.Soundness
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.AcceptSound.compileFunBody-aux-success
d_compileFunBody'45'aux'45'success_34 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'aux'45'success_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8 ~v9 ~v10
  = du_compileFunBody'45'aux'45'success_34 v8
du_compileFunBody'45'aux'45'success_34 ::
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_310 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'aux'45'success_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.compileFunBody-sound
d_compileFunBody'45'sound_90 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'sound_90 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'sound_90 v1 v2 v3 v4 v5 v6
du_compileFunBody'45'sound_90 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'sound_90 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_compileFunBody'45'aux'45'success_34
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1278
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
               (coe v5) (coe v4))))
      (coe
         MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_390
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
         (coe v5) (coe v4))
-- Once.Adequacy.AcceptSound.compileFun-main-aux-sound
d_compileFun'45'main'45'aux'45'sound_140 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'sound_140 ~v0 v1 v2 v3 v4 v5 v6 v7
                                         ~v8 ~v9
  = du_compileFun'45'main'45'aux'45'sound_140 v1 v2 v3 v4 v5 v6 v7
du_compileFun'45'main'45'aux'45'sound_140 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'sound_140 v0 v1 v2 v3 v4 v5 v6
  = coe
      seq (coe v6)
      (coe
         du_compileFunBody'45'sound_90 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5))
-- Once.Adequacy.AcceptSound.compileFun-aux-sound
d_compileFun'45'aux'45'sound_194 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'sound_194 ~v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'sound_194 v1 v2 v3 v4 v5 v6 v7
du_compileFun'45'aux'45'sound_194 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'sound_194 v0 v1 v2 v3 v4 v5 v6
  = if coe v6
      then coe
             du_compileFun'45'main'45'aux'45'sound_140 (coe v0) (coe v1)
             (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v4))
      else coe
             du_compileFunBody'45'sound_90 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5)
-- Once.Adequacy.AcceptSound.compileFun-sound
d_compileFun'45'sound_246 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'sound_246 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'sound_246 v1 v2 v3 v4 v5 v6
du_compileFun'45'sound_246 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'sound_246 v0 v1 v2 v3 v4 v5
  = coe
      du_compileFun'45'aux'45'sound_194 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v3)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.AcceptSound.caf-go-sound
d_caf'45'go'45'sound_276 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
d_caf'45'go'45'sound_276 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_caf'45'go'45'sound_276 v0 v1 v2 v3 v4
du_caf'45'go'45'sound_276 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
du_caf'45'go'45'sound_276 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe MAlonzo.Code.Once.Spec.Module.C_tnil_18
      (:) v5 v6
        -> coe
             du_caf'45'go'45'rf'45'sound_312 (coe v0) (coe v1) (coe v2) (coe v5)
             (coe v6) (coe v4)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_340 (coe v4) (coe v1)
                (coe MAlonzo.Code.Once.Parser.d_funType_110 (coe v5))
                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.caf-go-cf-sound
d_caf'45'go'45'cf'45'sound_294 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
d_caf'45'go'45'cf'45'sound_294 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
  = du_caf'45'go'45'cf'45'sound_294 v0 v1 v2 v3 v4 v5 v6
du_caf'45'go'45'cf'45'sound_294 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
du_caf'45'go'45'cf'45'sound_294 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.Compile.d_compileFun'45'aux_174
              (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0) (coe v5) (coe v1)
              (coe v2) (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3))
              (coe v6) (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                 (coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                         (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                       (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          (MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                          ("main" :: Data.Text.Text))))) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8 -> erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> let v9
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_372
                        (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0) (coe v1) (coe v2)
                        (coe v4)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                           (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)) in
              coe
                (case coe v9 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                     -> coe
                          MAlonzo.Code.Once.Spec.Module.C_tcons_30 v6
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                du_compileFun'45'sound_246 (coe v5) (coe v1) (coe v2)
                                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)
                                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_compileFun'45'sound_246 (coe v5) (coe v1) (coe v2)
                                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)
                                (coe MAlonzo.Code.Once.Parser.d_funBody_114 (coe v3))))
                          (coe
                             du_caf'45'go'45'sound_276 (coe v0) (coe v1) (coe v2) (coe v4)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_50 (coe v5)
                                (coe MAlonzo.Code.Once.Parser.d_funName_108 (coe v3)) (coe v6)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.AcceptSound.caf-go-rf-sound
d_caf'45'go'45'rf'45'sound_312 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
d_caf'45'go'45'rf'45'sound_312 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
  = du_caf'45'go'45'rf'45'sound_312 v0 v1 v2 v3 v4 v5 v6
du_caf'45'go'45'rf'45'sound_312 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
du_caf'45'go'45'rf'45'sound_312 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             du_caf'45'go'45'cf'45'sound_294 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v5) (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.caf-sound
d_caf'45'sound_502 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
d_caf'45'sound_502 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'sound_502 v0 v1 v2 v3
du_caf'45'sound_502 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_10
du_caf'45'sound_502 v0 v1 v2 v3
  = coe
      du_caf'45'go'45'sound_276 (coe v0) (coe v2) (coe v3) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_48)
-- Once.Adequacy.AcceptSound.crm-aux-sound
d_crm'45'aux'45'sound_522 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'aux'45'sound_522 v0 v1 v2 ~v3 ~v4
  = du_crm'45'aux'45'sound_522 v0 v1 v2
du_crm'45'aux'45'sound_522 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_crm'45'aux'45'sound_522 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_caf'45'sound_502 (coe v0) (coe v4)
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_270 (coe v5))
                    (coe
                       MAlonzo.Code.Once.Compile.d_collectSigEffects_498
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.crm-sound
d_crm'45'sound_546 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_230] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'sound_546 v0 v1 ~v2 ~v3 = du_crm'45'sound_546 v0 v1
du_crm'45'sound_546 ::
  Bool -> MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> AgdaAny
du_crm'45'sound_546 v0 v1
  = coe
      du_crm'45'aux'45'sound_522 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_540
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
-- Once.Adequacy.AcceptSound.moduleToIR-typed
d_moduleToIR'45'typed_558 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'typed_558 v0 ~v1 ~v2
  = du_moduleToIR'45'typed_558 v0
du_moduleToIR'45'typed_558 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> AgdaAny
du_moduleToIR'45'typed_558 v0
  = coe
      du_crm'45'sound_546 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe v0)
