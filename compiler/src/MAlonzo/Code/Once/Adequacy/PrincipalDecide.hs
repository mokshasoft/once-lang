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

module MAlonzo.Code.Once.Adequacy.PrincipalDecide where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate

-- Once.Adequacy.PrincipalDecide.fails
d_fails_12 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 -> Bool
d_fails_12 ~v0 ~v1 ~v2 v3 = du_fails_12 v3
du_fails_12 ::
  MAlonzo.Code.Once.TypeCheck.Elaborate.T_CheckElabResult_98 -> Bool
du_fails_12 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v1 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.PrincipalDecide.firstChecking-sound
d_firstChecking'45'sound_24 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Internal.Type.T_Type_8] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_firstChecking'45'sound_24 = erased
-- Once.Adequacy.PrincipalDecide.fc-step-sound
d_fc'45'step'45'sound_40 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Internal.Type.T_Type_8] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_fc'45'step'45'sound_40 = erased
-- Once.Adequacy.PrincipalDecide.firstChecking-complete
d_firstChecking'45'complete_114 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Internal.Type.T_Type_8] ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_firstChecking'45'complete_114 = erased
-- Once.Adequacy.PrincipalDecide.fc-step-complete
d_fc'45'step'45'complete_130 ::
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  [MAlonzo.Code.Once.Internal.Type.T_Type_8] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fc'45'step'45'complete_130 = erased
