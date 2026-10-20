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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Principal
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Honest
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Soundness
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.AcceptSound.compileFunBody-aux-success
d_compileFunBody'45'aux'45'success_36 ::
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
d_compileFunBody'45'sound_96 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8
  = du_compileFunBody'45'sound_96 v1 v2 v5 v6
du_compileFunBody'45'sound_96 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBody'45'sound_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            du_compileFunBody'45'aux'45'success_36
            (coe
               MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                  (coe v0) (coe v1))
               (coe v3) (coe v2))))
      (coe
         MAlonzo.Code.Once.TypeCheck.Soundness.du_check'45'sound_2432
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v0) (coe v1))
         (coe v3) (coe v2))
-- Once.Adequacy.AcceptSound.compileFun-main-aux-sound
d_compileFun'45'main'45'aux'45'sound_146 ::
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
d_compileFun'45'main'45'aux'45'sound_146 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7
                                         ~v8 ~v9
  = du_compileFun'45'main'45'aux'45'sound_146 v1 v2 v5 v6 v7
du_compileFun'45'main'45'aux'45'sound_146 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
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
d_compileFun'45'aux'45'sound_200 ~v0 v1 v2 ~v3 ~v4 v5 v6 v7 ~v8 ~v9
  = du_compileFun'45'aux'45'sound_200 v1 v2 v5 v6 v7
du_compileFun'45'aux'45'sound_200 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'aux'45'sound_200 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_compileFun'45'main'45'aux'45'sound_146 (coe v0) (coe v1)
             (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v2))
      else coe
             du_compileFunBody'45'sound_96 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.AcceptSound.compileFun-sound
d_compileFun'45'sound_252 ::
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
d_compileFun'45'sound_252 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8
  = du_compileFun'45'sound_252 v1 v2 v4 v5 v6
du_compileFun'45'sound_252 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFun'45'sound_252 v0 v1 v2 v3 v4
  = coe
      du_compileFun'45'aux'45'sound_200 (coe v0) (coe v1) (coe v3)
      (coe v4)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.AcceptSound.compileFunBodyI-at-success
d_compileFunBodyI'45'at'45'success_298 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_compileFunBodyI'45'at'45'success_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13 ~v14
  = du_compileFunBodyI'45'at'45'success_298 v11 v12
du_compileFunBodyI'45'at'45'success_298 ::
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_compileFunBodyI'45'at'45'success_298 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> coe seq (coe v2) (coe seq (coe v3) (coe v0))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.compileFunBodyI-aux-success
d_compileFunBodyI'45'aux'45'success_356 ::
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
d_compileFunBodyI'45'aux'45'success_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        v7 ~v8 v9 ~v10 ~v11
  = du_compileFunBodyI'45'aux'45'success_356 v7 v9
du_compileFunBodyI'45'aux'45'success_356 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunBodyI'45'aux'45'success_356 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_88 v4 v5 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       du_compileFunBodyI'45'at'45'success_298 (coe v3)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__216 (coe v4)
                          (coe v0)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.compileFunI-sound
d_compileFunI'45'sound_420 ::
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
d_compileFunI'45'sound_420 ~v0 v1 v2 ~v3 v4 v5 v6 ~v7 ~v8
  = du_compileFunI'45'sound_420 v1 v2 v4 v5 v6
du_compileFunI'45'sound_420 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compileFunI'45'sound_420 v0 v1 v2 v3 v4
  = coe
      du_aux_466 (coe v0) (coe v1) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v2)
         (coe ("main" :: Data.Text.Text)))
-- Once.Adequacy.AcceptSound._.body
d_body_446 ::
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
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_body_446 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_body_446 v1 v2 v5 v6
du_body_446 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_body_446 v0 v1 v2 v3
  = coe
      du_compileFunBodyI'45'aux'45'success_356 (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe v0) (coe v1))
         (coe v3))
-- Once.Adequacy.AcceptSound._.main
d_main_456 ::
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
d_main_456 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_main_456 v1 v2 v5 v6 v9
du_main_456 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_main_456 v0 v1 v2 v3 v4
  = coe
      seq (coe v4) (coe du_body_446 (coe v0) (coe v1) (coe v2) (coe v3))
-- Once.Adequacy.AcceptSound._.aux
d_aux_466 ::
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
d_aux_466 ~v0 v1 v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 ~v10 ~v11
  = du_aux_466 v1 v2 v5 v6 v9
du_aux_466 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_466 v0 v1 v2 v3 v4
  = if coe v4
      then coe
             du_main_456 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Compile.d_validateMain_20 (coe v2))
      else coe du_body_446 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.AcceptSound.compileFunM-sound
d_compileFunM'45'sound_492 ::
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
d_compileFunM'45'sound_492 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             (\ v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
                coe du_compileFun'45'sound_252 v3 v4 v6 v7 v8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             (\ v1 v2 v3 v4 v5 v6 v7 v8 v9 ->
                coe du_compileFunI'45'sound_420 v2 v3 v5 v6 v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.scopeOf
d_scopeOf_494 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Module.T_Scope_6
d_scopeOf_494 v0
  = coe
      MAlonzo.Code.Once.Lang.Module.C_scope_20
      (coe MAlonzo.Code.Once.Compile.d_csig_630 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v0))
      (coe
         MAlonzo.Code.Once.Compile.d_telePolys_644
         (MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0)))
-- Once.Adequacy.AcceptSound.consCF-inj
d_consCF'45'inj_506 ::
  MAlonzo.Code.Once.Compile.T_CompiledFun_524 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consCF'45'inj_506 ~v0 v1 ~v2 ~v3 = du_consCF'45'inj_506 v1
du_consCF'45'inj_506 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consCF'45'inj_506 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-sound
d_ce'45'sound_518 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_ce'45'sound_518 v0 v1 v2 v3 ~v4 = du_ce'45'sound_518 v0 v1 v2 v3
du_ce'45'sound_518 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_ce'45'sound_518 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe MAlonzo.Code.Once.Lang.Module.C_'91''93'_74
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v6
               -> coe
                    du_ce'45'fun'45'sound_532 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v6))
                    (coe v3)
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v6
               -> coe
                    du_ce'45'poly'45'sound_572 (coe v0) (coe v1) (coe v6) (coe v5)
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-fun-sound
d_ce'45'fun'45'sound_532 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_ce'45'fun'45'sound_532 v0 v1 v2 v3 v4 ~v5 v6 ~v7
  = du_ce'45'fun'45'sound_532 v0 v1 v2 v3 v4 v6
du_ce'45'fun'45'sound_532 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_ce'45'fun'45'sound_532 v0 v1 v2 v3 v4 v5
  = if coe v4
      then coe
             du_ce'45'prim'45'sound_546 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2)) (coe v5)
      else coe
             du_ce'45'mono'45'sound_560 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.Compile.d_resolveFunType_594
                (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
-- Once.Adequacy.AcceptSound.ce-prim-sound
d_ce'45'prim'45'sound_546 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_ce'45'prim'45'sound_546 v0 v1 v2 v3 ~v4 v5 ~v6 v7 ~v8
  = du_ce'45'prim'45'sound_546 v0 v1 v2 v3 v5 v7
du_ce'45'prim'45'sound_546 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_ce'45'prim'45'sound_546 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_conc_664 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
             (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v6))
             (coe MAlonzo.Code.Once.Lang.Type.Honest.d_honest'63'_202 (coe v6))
             (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v6))
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-mono-sound
d_ce'45'mono'45'sound_560 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_ce'45'mono'45'sound_560 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8
  = du_ce'45'mono'45'sound_560 v0 v1 v2 v3 v5
du_ce'45'mono'45'sound_560 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_ce'45'mono'45'sound_560 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe
             du_pstep_712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
             (coe
                MAlonzo.Code.Once.Compile.d_firstChecking_28
                (coe du_ctx_706 (coe v1))
                (coe MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2))
                (coe MAlonzo.Code.Once.Lang.Principal.d_below_10 (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.ce-poly-sound
d_ce'45'poly'45'sound_572 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_ce'45'poly'45'sound_572 v0 v1 v2 v3 v4 ~v5
  = du_ce'45'poly'45'sound_572 v0 v1 v2 v3 v4
du_ce'45'poly'45'sound_572 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_ce'45'poly'45'sound_572 v0 v1 v2 v3 v4
  = coe
      du_pstep_794 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Compile.d_firstChecking_28
         (coe du_ctx_766 (coe v1))
         (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v2))
         (coe du_low_768 (coe v2)))
      (coe v4)
-- Once.Adequacy.AcceptSound._.conc
d_conc_664 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_conc_664 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 v11 ~v12 v13 ~v14
           v15 ~v16
  = du_conc_664 v0 v1 v2 v3 v5 v9 v11 v13 v15
du_conc_664 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  Maybe AgdaAny ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_conc_664 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                      -> coe
                           MAlonzo.Code.Once.Lang.Module.C_ffi_84 v4 v9 v10 v11
                           (coe
                              du_ce'45'sound_518 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v1)
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                              (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._.ctx
d_ctx_706 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_706 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_ctx_706 v1
du_ctx_706 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_706 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
      (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
-- Once.Adequacy.AcceptSound._.pstep
d_pstep_712 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_pstep_712 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du_pstep_712 v0 v1 v2 v3 v5 v9
du_pstep_712 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_pstep_712 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v5)
      (coe
         du_grd_718 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Once.Type.Rigid.d_rigidFree'63'_676 (coe v4)))
-- Once.Adequacy.AcceptSound._.grd
d_grd_718 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_grd_718 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12
  = du_grd_718 v0 v1 v2 v3 v5 v10
du_grd_718 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_grd_718 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             du_step_740 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
             (coe
                MAlonzo.Code.Once.Compile.d_compileFunM_522
                (MAlonzo.Code.Once.Parser.d_funType_108 (coe v2))
                (coe MAlonzo.Code.Once.IR.C_Heap_8) v0
                (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                (MAlonzo.Code.Once.Compile.d_declImps_650
                   (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) v4
                (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._._.step
d_step_740 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_step_740 v0 v1 v2 v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 v13
           ~v14 ~v15 ~v16
  = du_step_740 v0 v1 v2 v3 v5 v10 v13
du_step_740 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_step_740 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             MAlonzo.Code.Once.Lang.Module.C_mono_96 v4
             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   d_compileFunM'45'sound_492
                   (MAlonzo.Code.Once.Parser.d_funType_108 (coe v2)) v0
                   (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                   (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                   (MAlonzo.Code.Once.Compile.d_declImps_650
                      (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                   (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) v4
                   (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)) v7 erased))
             v5
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                (coe
                   d_compileFunM'45'sound_492
                   (MAlonzo.Code.Once.Parser.d_funType_108 (coe v2)) v0
                   (MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                   (MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                   (MAlonzo.Code.Once.Compile.d_declImps_650
                      (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                   (MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) v4
                   (MAlonzo.Code.Once.Parser.d_funBody_110 (coe v2)) v7 erased))
             (coe
                du_ce'45'sound_518 (coe v0)
                (coe
                   MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      du_consCF'45'inj_506
                      (coe
                         MAlonzo.Code.Once.Compile.d_compileEntries_732
                         (coe MAlonzo.Code.Once.IR.C_Heap_8) (coe v0)
                         (coe
                            MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                         (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._.ctx
d_ctx_766 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
d_ctx_766 ~v0 v1 ~v2 ~v3 ~v4 ~v5 = du_ctx_766 v1
du_ctx_766 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104
du_ctx_766 v0
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
      (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
-- Once.Adequacy.AcceptSound._.low
d_low_768 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Lang.Type.T_Type_8]
d_low_768 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_low_768 v2
du_low_768 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Lang.Type.T_Type_8]
du_low_768 v0
  = coe
      MAlonzo.Code.Once.Lang.Principal.d_below_10
      (coe
         MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
         (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)))
-- Once.Adequacy.AcceptSound._.step
d_step_774 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_step_774 v0 v1 v2 v3 ~v4 ~v5 ~v6 v7 ~v8 v9 ~v10
  = du_step_774 v0 v1 v2 v3 v7 v9
du_step_774 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_step_774 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v8 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.Lang.Module.C_poly_106 v8 v7
                    (coe
                       du_ce'45'sound_518 (coe v0)
                       (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v1) (coe v2))
                       (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound._.pstep
d_pstep_794 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_pstep_794 v0 v1 v2 v3 ~v4 ~v5 v6 ~v7 v8 ~v9
  = du_pstep_794 v0 v1 v2 v3 v6 v8
du_pstep_794 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_pstep_794 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v4)
      (coe
         du_step_774 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
            (coe du_ctx_766 (coe v1))
            (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v2))
            (coe
               MAlonzo.Code.Once.Lang.Type.Instance.d_rigidOf_130
               (coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v2))))
         (coe v5))
-- Once.Adequacy.AcceptSound.crm-aux-sound
d_crm'45'aux'45'sound_808 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'aux'45'sound_808 v0 ~v1 v2 v3 ~v4
  = du_crm'45'aux'45'sound_808 v0 v2 v3
du_crm'45'aux'45'sound_808 ::
  Bool ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] -> AgdaAny
du_crm'45'aux'45'sound_808 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             du_ce'45'sound_518 (coe v0)
             (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638) (coe v3) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.AcceptSound.crm-sound
d_crm'45'sound_830 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_crm'45'sound_830 v0 v1 v2 ~v3 = du_crm'45'sound_830 v0 v1 v2
du_crm'45'sound_830 ::
  Bool ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524] -> AgdaAny
du_crm'45'sound_830 v0 v1 v2
  = coe
      du_crm'45'aux'45'sound_808 (coe v0)
      (coe
         MAlonzo.Code.Once.Parser.d_extractFunctions_632
         (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v1))
         (coe v1))
      (coe v2)
-- Once.Adequacy.AcceptSound.moduleToIR-typed
d_moduleToIR'45'typed_842 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_moduleToIR'45'typed_842 v0 ~v1 ~v2
  = du_moduleToIR'45'typed_842 v0
du_moduleToIR'45'typed_842 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> AgdaAny
du_moduleToIR'45'typed_842 v0
  = coe
      du_crm'45'sound_830 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Once.Adequacy.MainBuilds.du_moduleToIR'45'inj'8322'_944
            (coe v0)))
