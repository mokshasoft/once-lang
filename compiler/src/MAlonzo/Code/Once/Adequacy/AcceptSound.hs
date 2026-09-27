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
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'aux'45'success_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 v8 ~v9 ~v10
  = du_compileFunBody'45'aux'45'success_34 v8
du_compileFunBody'45'aux'45'success_34 ::
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'aux'45'success_34 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.compileFunBody-sound
d_compileFunBody'45'sound_88 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFunBody'45'sound_88 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_compileFunBody'45'sound_88 v1 v2 v3 v4 v5
du_compileFunBody'45'sound_88 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'sound_88 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_compileFunBody'45'aux'45'success_34
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab_1360
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
                  (coe v0) (coe v1) (coe v2) (coe v3))
               (coe v4) (coe v3))))
      (coe
         MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2532
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndSelfAndPolys_352
            (coe v0) (coe v1) (coe v2) (coe v3))
         (coe v4) (coe v3))
-- Once.Adequacy.AcceptSound.compileFun-main-aux-sound
d_compileFun'45'main'45'aux'45'sound_134 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'main'45'aux'45'sound_134 ~v0 v1 v2 v3 v4 v5 v6 ~v7
                                         ~v8
  = du_compileFun'45'main'45'aux'45'sound_134 v1 v2 v3 v4 v5 v6
du_compileFun'45'main'45'aux'45'sound_134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'main'45'aux'45'sound_134 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (coe
         du_compileFunBody'45'sound_88 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Once.Adequacy.AcceptSound.compileFun-aux-sound
d_compileFun'45'aux'45'sound_182 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'aux'45'sound_182 ~v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'aux'45'sound_182 v1 v2 v3 v4 v5 v6
du_compileFun'45'aux'45'sound_182 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'sound_182 v0 v1 v2 v3 v4 v5
  = if coe v5
      then coe
             du_compileFun'45'main'45'aux'45'sound_134 (coe v0) (coe v1)
             (coe v2) (coe v3) (coe v4)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_4 (coe v3))
      else coe
             du_compileFunBody'45'sound_88 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4)
-- Once.Adequacy.AcceptSound.compileFun-sound
d_compileFun'45'sound_228 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileFun'45'sound_228 ~v0 v1 v2 v3 v4 v5 ~v6 ~v7
  = du_compileFun'45'sound_228 v1 v2 v3 v4 v5
du_compileFun'45'sound_228 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'sound_228 v0 v1 v2 v3 v4
  = coe
      du_compileFun'45'aux'45'sound_182 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.AcceptSound.caf-go-sound
d_caf'45'go'45'sound_254 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
d_caf'45'go'45'sound_254 v0 v1 v2 v3 ~v4 ~v5
  = du_caf'45'go'45'sound_254 v0 v1 v2 v3
du_caf'45'go'45'sound_254 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
du_caf'45'go'45'sound_254 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe MAlonzo.Code.Once.Spec.Module.C_tnil_14
      (:) v4 v5
        -> coe
             du_caf'45'go'45'rf'45'sound_286 (coe v0) (coe v1) (coe v4) (coe v5)
             (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_344 (coe v3) (coe v1)
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v4))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.caf-go-cf-sound
d_caf'45'go'45'cf'45'sound_270 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
d_caf'45'go'45'cf'45'sound_270 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_caf'45'go'45'cf'45'sound_270 v0 v1 v2 v3 v4 v5
du_caf'45'go'45'cf'45'sound_270 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
du_caf'45'go'45'cf'45'sound_270 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.Compile.du_compileFun'45'aux_184 (coe v0)
              (coe v4) (coe v1)
              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
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
                    = MAlonzo.Code.Once.Compile.d_compileAllFuns'45'go_376
                        (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0) (coe v1) (coe v3)
                        (coe
                           MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> erased
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                     -> coe
                          MAlonzo.Code.Once.Spec.Module.C_tcons_26 v5
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                du_compileFun'45'sound_228 (coe v4) (coe v1)
                                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
                                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_compileFun'45'sound_228 (coe v4) (coe v1)
                                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)
                                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))))
                          (coe
                             du_caf'45'go'45'sound_254 (coe v0) (coe v1) (coe v3)
                             (coe
                                MAlonzo.Code.Once.Compile.d_extendFunCtx_66 (coe v4)
                                (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v5)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.AcceptSound.caf-go-rf-sound
d_caf'45'go'45'rf'45'sound_286 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
d_caf'45'go'45'rf'45'sound_286 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
  = du_caf'45'go'45'rf'45'sound_286 v0 v1 v2 v3 v4 v5
du_caf'45'go'45'rf'45'sound_286 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
du_caf'45'go'45'rf'45'sound_286 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
        -> coe
             du_caf'45'go'45'cf'45'sound_270 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe v4) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.caf-sound
d_caf'45'sound_456 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
d_caf'45'sound_456 v0 v1 v2 ~v3 ~v4 = du_caf'45'sound_456 v0 v1 v2
du_caf'45'sound_456 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_FunInfo_96] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Module.T_AllFunsTyped_8
du_caf'45'sound_456 v0 v1 v2
  = coe
      du_caf'45'go'45'sound_254 (coe v0) (coe v2) (coe v1)
      (coe MAlonzo.Code.Once.Compile.d_emptyFunCtx_64)
-- Once.Adequacy.AcceptSound.crm-aux-sound
d_crm'45'aux'45'sound_474 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'aux'45'sound_474 v0 ~v1 v2 ~v3 ~v4
  = du_crm'45'aux'45'sound_474 v0 v2
du_crm'45'aux'45'sound_474 ::
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_crm'45'aux'45'sound_474 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    du_caf'45'sound_456 (coe v0) (coe v3)
                    (coe MAlonzo.Code.Once.Compile.d_buildPolyCtx_274 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.crm-sound
d_crm'45'sound_498 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_234] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'sound_498 v0 v1 ~v2 ~v3 = du_crm'45'sound_498 v0 v1
du_crm'45'sound_498 ::
  Bool -> MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny
du_crm'45'sound_498 v0 v1
  = coe
      du_crm'45'aux'45'sound_474 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_514
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
-- Once.Adequacy.AcceptSound.moduleToIR-typed
d_moduleToIR'45'typed_510 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'typed_510 v0 ~v1 ~v2
  = du_moduleToIR'45'typed_510 v0
du_moduleToIR'45'typed_510 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny
du_moduleToIR'45'typed_510 v0
  = coe
      du_crm'45'sound_498 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe v0)
