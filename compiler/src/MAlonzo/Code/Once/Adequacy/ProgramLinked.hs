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

module MAlonzo.Code.Once.Adequacy.ProgramLinked where

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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.AcceptSound
import qualified MAlonzo.Code.Once.Adequacy.ElaborateLinked
import qualified MAlonzo.Code.Once.Adequacy.EntriesValid
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Instance
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ProgramLinked.ImpRef
d_ImpRef_8 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_ImpRef_8 = erased
-- Once.Adequacy.ProgramLinked.FFIRef
d_FFIRef_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_FFIRef_16 = erased
-- Once.Adequacy.ProgramLinked.PolyRef
d_PolyRef_24 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_PolyRef_24 = erased
-- Once.Adequacy.ProgramLinked.spliceWith
d_spliceWith_48 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceWith_48 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_spliceWith_48 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_spliceWith_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_spliceWith_48 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v11 v12 v13 v14
               -> coe
                    seq (coe v11)
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_406
                       (coe
                          MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExprWF_3272
                          (coe v5) (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                (coe (0 :: Integer)) (coe v6) (coe v0))
                             (coe v7) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v10))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v11
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.SpliceOK
d_SpliceOK_80 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_SpliceOK_80 = erased
-- Once.Adequacy.ProgramLinked.Refs-substA
d_Refs'45'substA_130 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Refs'45'substA_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_Refs'45'substA_130 v10
du_Refs'45'substA_130 :: AgdaAny -> AgdaAny
du_Refs'45'substA_130 v0 = coe v0
-- Once.Adequacy.ProgramLinked.Refs-substF
d_Refs'45'substF_160 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Refs'45'substF_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_Refs'45'substF_160 v11
du_Refs'45'substF_160 :: AgdaAny -> AgdaAny
du_Refs'45'substF_160 v0 = coe v0
-- Once.Adequacy.ProgramLinked.Linked-substˡ
d_Linked'45'subst'737'_182 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_Linked'45'subst'737'_182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_Linked'45'subst'737'_182 v7
du_Linked'45'subst'737'_182 :: AgdaAny -> AgdaAny
du_Linked'45'subst'737'_182 v0 = coe v0
-- Once.Adequacy.ProgramLinked.Linked-substʳ
d_Linked'45'subst'691'_202 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_Linked'45'subst'691'_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_Linked'45'subst'691'_202 v7
du_Linked'45'subst'691'_202 :: AgdaAny -> AgdaAny
du_Linked'45'subst'691'_202 v0 = coe v0
-- Once.Adequacy.ProgramLinked.RR
d_RR_214 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> ()
d_RR_214 = erased
-- Once.Adequacy.ProgramLinked.realize-refs
d_realize'45'refs_228 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny
d_realize'45'refs_228 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v9 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            d_realize'45'refs_228 (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                               (coe v22))
                                            (coe v12) (coe v15))
                                         (coe
                                            d_realize'45'refs'45'd_256 (coe v0) (coe v17) (coe v20)
                                            (coe v9) (coe v24) (coe v13) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v9 v11 v13 v14 v15 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v23 v24 v25
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v26 v27
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            d_realize'45'refs'45'i_240 (coe v0) (coe v22)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                               (coe v11))
                                            (coe v14) (coe v16))
                                         (coe
                                            d_realize'45'refs_228 (coe v0) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v27))
                                               (coe v9))
                                            (coe v15) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v12) (coe v14))
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Type.C__'42'__124 v25 v26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v24))
                                                      (coe v25))
                                                   (coe v12) (coe v14))
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v24))
                                                      (coe v26))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                    -> coe
                                         d_realize'45'refs_228 (coe v0) (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'42'__124 (coe v16)
                                               (coe v19))
                                            (coe
                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                            (coe v21))
                                         (coe v3) (coe v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v18
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                                    -> coe
                                         d_realize'45'refs_228 (coe v0) (coe v14)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                            (coe
                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                               (coe v18) (coe v17))
                                            (coe
                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                            (coe v17))
                                         (coe v3) (coe v12)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_606 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v18 v19
                             -> coe
                                  d_realize'45'refs_228
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400 (coe v0))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402 (coe v0)))
                                  (coe v14)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v18)
                                        (coe v15)))
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_392
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_imports_400
                                              (coe v0))
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.d_polys_402
                                              (coe v0)))))
                                  (coe v12)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v7 v10 v11
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1) (coe v7) (coe v3)
             (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> coe
                           d_realize'45'refs_228
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                              (coe v16) (coe v18))
                           (coe v17) (coe v20)
                           (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v3)
                           (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_654 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v14) (coe v16) (coe v10)
                              (coe v12))
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v15) (coe v17) (coe v11)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_664 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v13) (coe v2))
                              (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_676 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_688 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12) (coe v13) (coe v9)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_700 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12) (coe v14) (coe v9)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_710 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs_228 (coe v0) (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724 v8 v9 v10 v15
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10)))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.realize-refs-i
d_realize'45'refs'45'i_240 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny
d_realize'45'refs'45'i_240 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v9
        -> coe seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v10
        -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.CanonicalName.C_canonical_10 v12
                      -> case coe v12 of
                           [] -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                           (:) v13 v14
                             -> case coe v14 of
                                  [] -> erased
                                  (:) v15 v16
                                    -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_88 v11
        -> erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_104 v8 v9 v10 v11 v15
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_458))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_114 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    d_realize'45'refs_228 (coe v0) (coe v11) (coe v2) (coe v3)
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              d_realize'45'refs'45'i_240 (coe v0) (coe v14) (coe v16) (coe v10)
                              (coe v12))
                           (coe
                              d_realize'45'refs'45'i_240 (coe v0) (coe v15) (coe v17) (coe v11)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_138 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    d_realize'45'refs'45'i_240 (coe v0) (coe v10)
                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_150
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_170 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v17) (coe v9) (coe v12)
                       (coe v14))
                    (coe
                       d_realize'45'refs'45'i_240
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                          (coe v16) (coe v9))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_200 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v11) (coe v12))
                       (coe v16) (coe v19))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                             (coe v23) (coe v11))
                          (coe v24) (coe v2)
                          (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v17)
                          (coe v20))
                       (coe
                          d_realize'45'refs'45'i_240
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                             (coe v25) (coe v12))
                          (coe v26) (coe v2)
                          (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18)
                          (coe v21)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_214 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_228 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_242 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_256 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_270 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_280 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v2) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_292 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_304 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_314 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v7) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           (coe
                              d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v7)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v15))
                                 (coe v7))
                              (coe v9) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_350 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_362 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v7)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_380 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (coe
                       d_realize'45'refs_228 (coe v0) (coe v17) (coe v8) (coe v12)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_396 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v19))
                              (coe v10) (coe v13))
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v16) (coe v8) (coe v11)
                              (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_412 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'd_256 (coe v0) (coe v15) (coe v8) (coe v2)
                       (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v10) (coe v14))
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v16) (coe v8) (coe v11)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.realize-refs-d
d_realize'45'refs'45'd_256 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  AgdaAny
d_realize'45'refs'45'd_256 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_742 v10 v13 v15 v16 v17
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                (coe v3))
             (coe v5) (coe v15)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v12 v13 v14 v15 v16 v17 v22 v23 v24 v25
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v17)))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v24))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v12 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v17 v18
               -> coe
                    d_realize'45'refs'45'i_240
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                       (coe v17) (coe v2))
                    (coe v18) (coe v3)
                    (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v5)
                    (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804 v11 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              d_realize'45'refs'45'd_256 (coe v0) (coe v21) (coe v11) (coe v3)
                              (coe v4) (coe v14) (coe v17))
                           (coe
                              d_realize'45'refs'45'd_256 (coe v0) (coe v19) (coe v2) (coe v11)
                              (coe v4) (coe v15) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__126 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v21) (coe v22)
                                     (coe v3) (coe v4) (coe v14) (coe v16))
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v19) (coe v23)
                                     (coe v3) (coe v4) (coe v15) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v21) (coe v2)
                                     (coe v22) (coe v4) (coe v14) (coe v16))
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v19) (coe v2)
                                     (coe v23) (coe v4) (coe v15) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                      -> coe
                           d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17) (coe v3))
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                              (coe v3))
                           (coe v5) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.L
d_L_600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_L_600 = erased
-- Once.Adequacy.ProgramLinked._.as-case
d_as'45'case_628 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> AgdaAny) -> AgdaAny
d_as'45'case_628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 v17
  = du_as'45'case_628 v16 v17
du_as'45'case_628 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> AgdaAny) -> AgdaAny
du_as'45'case_628 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v4 v5 v6 v7
               -> coe seq (coe v4) (coe v1 erased)
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v4
               -> coe v1 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.rp-case
d_rp'45'case_682 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_rp'45'case_682 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14
  = du_rp'45'case_682 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_rp'45'case_682 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_rp'45'case_682 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> coe
                           du_as'45'case_628
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                                 (coe v0 v4) (coe v15))
                              (coe v14) (coe v5))
                           (coe (\ v16 -> coe v1 v4 v5 v10 v12 v14 v15 v9 v16 v2 v3 v6 v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v10 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
               -> coe
                    seq (coe v12) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._._.nothing≢just
d_nothing'8802'just_706 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_706 = erased
-- Once.Adequacy.ProgramLinked._.resolve-refs
d_resolve'45'refs_748 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_resolve'45'refs_748 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                      v13
  = du_resolve'45'refs_748 v2 v3 v4 v6 v7 v8 v9 v11 v12 v13
du_resolve'45'refs_748 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
du_resolve'45'refs_748 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v13 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
               -> coe
                    du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v6) (coe v20))
                    (coe v22) (coe v19) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v12 v13 v14 v16 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v16)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v7))
                       (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v14) (coe v18) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v12 v13 v14 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v20))
                              (coe v16) (coe v21))
                           (coe
                              du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v14) (coe v17) (coe v22))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v12 v13 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'42'__124 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v18) (coe v16) (coe v20))
                           (coe
                              du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v19) (coe v17) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v14 v15
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v7) (coe v14))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v13 v15
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v13) (coe v7))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_114 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
               -> coe
                    du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v16) (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_126 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
               -> coe
                    du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v17) (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v12 v13 v14 v15 v16 v17 v18 v20 v21 v22
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
               -> case coe v24 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6)
                              (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v17) (coe v18))
                              (coe v20) (coe v23))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v6)
                                    (coe v17))
                                 (coe v7) (coe v21) (coe v25))
                              (coe
                                 du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v6)
                                    (coe v18))
                                 (coe v7) (coe v22) (coe v26)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unit_154
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_164 v14
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v14)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v12 v13 v14 v15 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15) (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v6) (coe v15))
                       (coe v7) (coe v18) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_186 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_float_194 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_add_204 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_272 v13
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_div_282 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v13
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_le_320 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v13 v15 v16
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v13) (coe v16) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v13 v14 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v13 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v12
        -> coe
             du_rp'45'case_682 (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
             (coe v7) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_144
                (coe v0) (coe v12))
             erased (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v13
        -> coe
             du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v7)
             (coe v13) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v15
        -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v12 v13 v15 v16
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                    (coe
                       du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13) (coe v16) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v12 v13 v15 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                        (coe v22))
                                     (coe v18) (coe v25))
                                  (coe
                                     du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                        (coe v15))
                                     (coe v19) (coe v26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v12 v13 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
               -> case coe v20 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v23 v24
                      -> case coe v21 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe v22))
                                            (coe v18) (coe v27))
                                         (coe
                                            du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v24)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe v22))
                                            (coe v19) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v12 v13 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                      -> case coe v22 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v25 v26
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                               (coe v25))
                                            (coe v18) (coe v27))
                                         (coe
                                            du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                               (coe v26))
                                            (coe v19) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_502 v18
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
               -> case coe v21 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v22 v23 v24
                      -> case coe v23 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                             -> coe
                                  du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                     (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v19) (coe v22))
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                     (coe v24))
                                  (coe v18) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v21)
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                     (coe v20))
                                  (coe v17) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_530 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
               -> case coe v20 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v21 v22
                      -> coe
                           du_resolve'45'refs_748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe (0 :: Integer))
                           (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v18)
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v21) (coe v18)))
                           (coe v17) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.dc-linked
d_dc'45'linked_1300 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_dc'45'linked_1300 ~v0 ~v1 v2 ~v3 v4 = du_dc'45'linked_1300 v2 v4
du_dc'45'linked_1300 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_dc'45'linked_1300 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_136 -> coe v1
      MAlonzo.Code.Once.Type.C_rigid_138 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.ref-entry
d_ref'45'entry_1420 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool -> AgdaAny
d_ref'45'entry_1420 ~v0 ~v1 v2 v3 v4 v5
  = du_ref'45'entry_1420 v2 v3 v4 v5
du_ref'45'entry_1420 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> Bool -> AgdaAny
du_ref'45'entry_1420 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
               -> coe
                    seq (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                          (coe
                             MAlonzo.Code.Once.Compile.d_irFunOf_842
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                                (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                                (coe v2) (coe v3))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_842
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2) (coe v3))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.RefLinked-mono
d_RefLinked'45'mono_1592 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_RefLinked'45'mono_1592 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RefLinked'45'mono_1592 v3 v4 v5
du_RefLinked'45'mono_1592 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_RefLinked'45'mono_1592 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linked'45'mono_88
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (coe
         MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v2)
         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1)))
-- Once.Adequacy.ProgramLinked.LInv
d_LInv_1606 a0 a1 a2 = ()
data T_LInv_1606
  = C_constructor_1670 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748)
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                       ((MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
                        MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                        MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                        MAlonzo.Code.Once.Type.T_PolyType_254 ->
                        MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
                        [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
                        [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                        Integer ->
                        Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny)
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
-- Once.Adequacy.ProgramLinked.LInv.irf
d_irf_1642 ::
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irf_1642 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.iself
d_iself_1644 ::
  T_LInv_1606 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_1644 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.imp-ok
d_imp'45'ok_1650 ::
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'ok_1650 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.tel-ok
d_tel'45'ok_1658 ::
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
d_tel'45'ok_1658 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.ent-ok
d_ent'45'ok_1662 ::
  T_LInv_1606 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ent'45'ok_1662 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.imp-ffi
d_imp'45'ffi_1668 ::
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_imp'45'ffi_1668 v0
  = case coe v0 of
      C_constructor_1670 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.SpliceOK-mono
d_SpliceOK'45'mono_1690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
d_SpliceOK'45'mono_1690 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                        v12 v13 v14 v15 v16 v17
  = du_SpliceOK'45'mono_1690
      v3 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_SpliceOK'45'mono_1690 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
du_SpliceOK'45'mono_1690 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
      (coe (\ v14 v15 v16 -> v16))
      (coe du_RefLinked'45'mono_1592 (coe v0))
      (coe du_RefLinked'45'mono_1592 (coe v0)) (coe v3)
      (coe
         du_spliceWith_48 (coe v7) (coe v1) (coe v10) (coe v11) (coe v2)
         (coe v3) (coe v1 v2) (coe v6)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
               (coe v1 v2) (coe v7))
            (coe v6) (coe v3)))
      (coe v4 v5 v6 v7 v8 v9 v10 v11 v12 v13)
-- Once.Adequacy.ProgramLinked.ents-cons
d_ents'45'cons_1744 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ents'45'cons_1744 ~v0 v1 v2 v3 v4
  = du_ents'45'cons_1744 v1 v2 v3 v4
du_ents'45'cons_1744 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ents'45'cons_1744 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe
         MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linked'45'mono_88
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
            (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v0))
         (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v0))
         (coe v2))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linked'45'mono_88
                 (coe
                    MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                    (coe v0))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4))
                 (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v4))))
         (coe v1) (coe v3))
-- Once.Adequacy.ProgramLinked.imp-cons
d_imp'45'cons_1774 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'cons_1774 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_imp'45'cons_1774 v3 v5 v6 v7 v8 v9 v10
du_imp'45'cons_1774 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_imp'45'cons_1774 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe v4)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe seq (coe v9) (coe v2)
                else coe
                       seq (coe v9)
                       (coe
                          du_RefLinked'45'mono_1592
                          (coe
                             MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                             (coe v1))
                          v4 v5 (coe v3 v4 v5 v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked.ffi-cons
d_ffi'45'cons_1854 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ffi'45'cons_1854 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_ffi'45'cons_1854 v2 v4 v5 v6 v7 v8 v9
du_ffi'45'cons_1854 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_ffi'45'cons_1854 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v7 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe v3)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe seq (coe v9) (coe v1 v6)
                else coe seq (coe v9) (coe v2 v3 v4 v5 v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked.linv-entry
d_linv'45'entry_1928 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  T_LInv_1606 -> T_LInv_1606
d_linv'45'entry_1928 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_linv'45'entry_1928 v2 v3 v4 v5 v6 v7 v8 v9 v10
du_linv'45'entry_1928 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  T_LInv_1606 -> T_LInv_1606
du_linv'45'entry_1928 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      C_constructor_1670
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v1)
         (coe v5) (coe d_irf_1642 (coe v8)))
      (coe d_iself_1644 (coe v8))
      (coe
         du_imp'45'cons_1774 (coe v1)
         (coe du_e_1956 (coe v1) (coe v2) (coe v3) (coe v4))
         (coe du_ref'45'entry_1420 (coe v1) (coe v2) (coe v3) (coe v4))
         (coe d_imp'45'ok_1650 (coe v8)))
      (coe
         (\ v9 v10 v11 v12 v13 ->
            coe
              du_SpliceOK'45'mono_1690
              (coe
                 MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                 (coe du_e_1956 (coe v1) (coe v2) (coe v3) (coe v4)))
              (coe v9) (coe v11) (coe v12)
              (coe d_tel'45'ok_1658 v8 v9 v10 v11 v12 v13)))
      (coe
         du_ents'45'cons_1744
         (coe du_e_1956 (coe v1) (coe v2) (coe v3) (coe v4)) (coe v0)
         (coe v6) (coe d_ent'45'ok_1662 (coe v8)))
      (coe
         du_ffi'45'cons_1854 (coe v1) (coe v7)
         (coe d_imp'45'ffi_1668 (coe v8)))
-- Once.Adequacy.ProgramLinked._.e
d_e_1956 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  T_LInv_1606 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_1956 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
  = du_e_1956 v3 v4 v5 v6
du_e_1956 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Bool -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_1956 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_842
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
         (coe v2) (coe v3))
-- Once.Adequacy.ProgramLinked.body-linked
d_body'45'linked_1984 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_body'45'linked_1984 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                      ~v12
  = du_body'45'linked_1984 v0 v1 v2 v3 v4 v5 v6
du_body'45'linked_1984 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> AgdaAny
du_body'45'linked_1984 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.d_elaborate'45'linked_2520
      (coe v0) (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
      (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
         (coe v5) (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_396
            (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
         (coe du_uf_2010 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                     (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1)))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_D'8242'_2008 (coe v1) (coe v5) (coe v6))))
      (coe
         du_resolve'45'refs_748
         (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_396
            (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
         (coe
            d_tel'45'ok_1658 v3
            (MAlonzo.Code.Once.Compile.d_declImps_396
               (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
            (d_iself_1644 (coe v3)))
         (coe du_uf_2010 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                     (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1)))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_D'8242'_2008 (coe v1) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
            (coe
               (\ v7 v8 v9 ->
                  coe
                    d_imp'45'ffi_1668 v3
                    (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v7)) v8
                    erased erased))
            (coe d_imp'45'ok_1650 (coe v3)) (coe (\ v7 v8 v9 -> v9)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1)))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_D'8242'_2008 (coe v1) (coe v5) (coe v6)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1))))
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v1)))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_D'8242'_2008 (coe v1) (coe v5) (coe v6)))))
-- Once.Adequacy.ProgramLinked._.D′
d_D'8242'_2008 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_2008 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_D'8242'_2008 v1 v5 v6
du_D'8242'_2008 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_2008 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_320
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
            (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0)))
         (coe v2) (coe v1))
-- Once.Adequacy.ProgramLinked._.uf
d_uf_2010 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_2010 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_uf_2010 v1 v4 v5
du_uf_2010 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_2010 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
-- Once.Adequacy.ProgramLinked.prim-linked
d_prim'45'linked_2028 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_prim'45'linked_2028 v0 v1 v2 v3 v4 v5
  = coe
      du_dc'45'linked_1300 (coe v3)
      (coe
         MAlonzo.Code.Once.Adequacy.ElaborateLinked.d_elaborate'45'linked_2520
         (coe v0) (coe v1) (coe MAlonzo.Code.Once.IR.C_Heap_8)
         (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe (0 :: Integer)))
         (coe v3)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
            (MAlonzo.Code.Once.CanonicalName.d_bare_12
               (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
            v4)
         (coe v5))
-- Once.Adequacy.ProgramLinked.splice-at
d_splice'45'at_2074 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_splice'45'at_2074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18
  = du_splice'45'at_2074 v16 v18
du_splice'45'at_2074 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_splice'45'at_2074 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v4 v5 v6 v7
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.linv-poly
d_linv'45'poly_2106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> T_LInv_1606
d_linv'45'poly_2106 ~v0 v1 ~v2 v3 v4
  = du_linv'45'poly_2106 v1 v3 v4
du_linv'45'poly_2106 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> T_LInv_1606
du_linv'45'poly_2106 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         (\ v3 v4 v5 ->
            coe
              C_constructor_1670 (coe d_irf_1642 (coe v5))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                 (coe
                    MAlonzo.Code.Once.Adequacy.TelePosition.du_iself'45'step_138
                    (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Adequacy.TelePosition.du_'43''43''8315''691'_170
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
                          (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0)))
                       (coe v4))
                    (coe d_iself_1644 (coe v5))))
              (coe d_imp'45'ok_1650 (coe v5))
              (\ v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ->
                 coe
                   du_tel'8242'_2198 (coe v0) (coe v1) (coe v5) v6 v7 v8 v9 v10 v11
                   v12 v13 v16 v17 v18 v19)
              (coe d_ent'45'ok_1662 (coe v5)) (coe d_imp'45'ffi_1668 (coe v5))))
-- Once.Adequacy.ProgramLinked._.y
d_y_2126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_y_2126 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_y_2126 v3
du_y_2126 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_y_2126 v0 = coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0)
-- Once.Adequacy.ProgramLinked._.scT
d_scT_2128 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> MAlonzo.Code.Once.Type.T_PolyType_254
d_scT_2128 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_scT_2128 v3
du_scT_2128 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
du_scT_2128 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)
-- Once.Adequacy.ProgramLinked._.bd
d_bd_2130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_bd_2130 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_bd_2130 v3
du_bd_2130 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
du_bd_2130 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v0)
-- Once.Adequacy.ProgramLinked._.polys
d_polys_2132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_2132 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_polys_2132 v1
du_polys_2132 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_polys_2132 v0
  = coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0)
-- Once.Adequacy.ProgramLinked._.imps
d_imps_2134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imps_2134 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_imps_2134 v1
du_imps_2134 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_imps_2134 v0
  = coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0)
-- Once.Adequacy.ProgramLinked._.head-ok
d_head'45'ok_2150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
d_head'45'ok_2150 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 ~v8 v9 v10 ~v11 ~v12
                  v13 v14 ~v15 ~v16
  = du_head'45'ok_2150 v1 v3 v6 v7 v9 v10 v13 v14
du_head'45'ok_2150 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer -> AgdaAny
du_head'45'ok_2150 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_splice'45'at_2074 (coe du_cr_2176 (coe v0) (coe v1) (coe v5))
      (coe
         du_resolve'45'refs_748 (coe du_polys_2132 (coe v0)) (coe v3)
         (coe d_tel'45'ok_1658 v2 v3 v4) (coe v6) (coe v7)
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
               (coe du_imps_2134 (coe v0)) (coe du_polys_2132 (coe v0))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                     (coe du_imps_2134 (coe v0)) (coe du_polys_2132 (coe v0))))
               (coe (0 :: Integer)) (coe du_imps_2134 (coe v0))
               (coe du_polys_2132 (coe v0)))
            (coe du_bd_2130 (coe v1)) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_w_2180 (coe v0) (coe v1) (coe v5)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
            (coe
               (\ v8 v9 v10 ->
                  coe
                    d_imp'45'ffi_1668 v2
                    (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v8)) v9
                    erased erased))
            (coe d_imp'45'ok_1650 (coe v2)) (coe (\ v8 v9 v10 -> v10)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe du_imps_2134 (coe v0)) (coe du_polys_2132 (coe v0))))
                  (coe (0 :: Integer)) (coe du_imps_2134 (coe v0))
                  (coe du_polys_2132 (coe v0)))
               (coe du_bd_2130 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_w_2180 (coe v0) (coe v1) (coe v5)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_404
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_396
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
                        (coe du_imps_2134 (coe v0)) (coe du_polys_2132 (coe v0))))
                  (coe (0 :: Integer)) (coe du_imps_2134 (coe v0))
                  (coe du_polys_2132 (coe v0)))
               (coe du_bd_2130 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_w_2180 (coe v0) (coe v1) (coe v5)))))
-- Once.Adequacy.ProgramLinked._._.D-A
d_D'45'A_2174 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_D'45'A_2174 ~v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
              ~v13 ~v14 ~v15 ~v16
  = du_D'45'A_2174 v1 v3 v4 v6 v11
du_D'45'A_2174 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'45'A_2174 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_20
      (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_392 (coe v0))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
      (coe du_scT_2128 (coe v1)) (coe d_irf_1642 (coe v3)) (coe v2)
      (coe v4)
-- Once.Adequacy.ProgramLinked._._.cr
d_cr_2176 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cr_2176 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16
  = du_cr_2176 v1 v3 v10
du_cr_2176 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cr_2176 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6172
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_412
         (coe du_imps_2134 (coe v0)) (coe du_polys_2132 (coe v0)))
      (coe du_bd_2130 (coe v1)) (coe v2)
-- Once.Adequacy.ProgramLinked._._.ce
d_ce_2178 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_2178 = erased
-- Once.Adequacy.ProgramLinked._._.w
d_w_2180 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_w_2180 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16
  = du_w_2180 v1 v3 v10
du_w_2180 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_w_2180 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_320
      (coe du_cr_2176 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ProgramLinked._.tel′
d_tel'8242'_2198 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
d_tel'8242'_2198 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 ~v15 ~v16 v17 v18 v19 v20
  = du_tel'8242'_2198
      v1 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v17 v18 v19 v20
du_tel'8242'_2198 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1606 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
du_tel'8242'_2198 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v17 v18
        -> let v19
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v19 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe du_y_2126 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                        (coe du_y_2126 (coe v1)) (coe v5)) in
           coe
             (case coe v19 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                  -> if coe v20
                       then coe
                              seq (coe v21)
                              (case coe v7 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                   -> coe
                                        seq (coe v23)
                                        (coe
                                           du_head'45'ok_2150 (coe v0) (coe v1) (coe v2) (coe v3)
                                           (coe v18) (coe v6) (coe v11) (coe v12))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       else coe
                              seq (coe v21)
                              (coe
                                 d_tel'45'ok_1658 v2 v3 v18 v5 v6 v7 v8 v9 v10 erased erased v11 v12
                                 v13 v14)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.link-walk
d_link'45'walk_2342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1606 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_link'45'walk_2342 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_'91''93'_42
        -> coe seq (coe v4) (coe d_ent'45'ok_1662 (coe v6))
      MAlonzo.Code.Once.Spec.Module.C_ffi_52 v12 v16 v17 v18 v19
        -> case coe v2 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v22
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v25 v27 v28 v29 v35
                             -> case coe v9 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v38 v39
                                    -> coe
                                         d_link'45'walk_2342 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Compile.C_cscope_386
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Parser.d_funName_106
                                                     (coe v22))
                                                  (coe v12))
                                               (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1)))
                                            (coe MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1)))
                                         (coe v21) (coe v19) (coe v35)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Once.Denotation.Program.C_irFun_24
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.d_funName_106
                                                        (coe v22))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Once.IR.C__'8728'__28
                                                           (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                              (coe v12)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                                                 (coe
                                                                    MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_106
                                                                          (coe v22))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                 v27))
                                                           (coe MAlonzo.Code.Once.IR.C_id_20)))))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                           (coe v12)
                                                           (coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__28
                                                              (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                                 (coe v12)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                                                    (coe
                                                                       MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Once.Parser.d_funName_106
                                                                             (coe v22))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                    v27))
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_id_20))))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Once.IR.C__'8728'__28
                                                           (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                              (coe v12)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                                                 (coe
                                                                    MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Once.Parser.d_funName_106
                                                                          (coe v22))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                 v27))
                                                           (coe MAlonzo.Code.Once.IR.C_id_20))))))
                                            (coe v5))
                                         (coe
                                            du_linv'45'entry_1928 (coe v5)
                                            (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v22))
                                            (coe v12)
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__28
                                               (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_384
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                  (coe v12)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380
                                                     (coe
                                                        MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Once.Parser.d_funName_106
                                                              (coe v22))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                     v27))
                                               (coe MAlonzo.Code.Once.IR.C_id_20))
                                            (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v18)
                                            (coe
                                               d_prim'45'linked_2028 (coe v0) (coe v5) (coe v22)
                                               (coe v12) (coe v27)
                                               (coe
                                                  v8
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Parser.d_funName_106
                                                        (coe v22))
                                                     (coe v12))
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                     erased)))
                                            (coe
                                               (\ v40 ->
                                                  coe
                                                    v8
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Parser.d_funName_106
                                                          (coe v22))
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                       erased)))
                                            (coe v6))
                                         (coe
                                            MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                                            (coe v21) (coe v7))
                                         (coe
                                            (\ v40 v41 ->
                                               coe
                                                 v8 v40
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                    v41)))
                                         (coe v39)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_mono_64 v12 v14 v17 v18 v19
        -> case coe v2 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v23 v24 v25 v26
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_64 v30 v31 v32 v33 v34 v35 v38 v42
                                    -> coe
                                         seq (coe v31)
                                         (case coe v9 of
                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v45 v46
                                              -> coe
                                                   d_link'45'walk_2342 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Compile.C_cscope_386
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v23) (coe v12))
                                                         (coe
                                                            MAlonzo.Code.Once.Compile.d_cimps_382
                                                            (coe v1)))
                                                      (coe
                                                         MAlonzo.Code.Once.Compile.d_ctele_384
                                                         (coe v1)))
                                                   (coe v21) (coe v19) (coe v42)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Program.C_irFun_24
                                                         (coe
                                                            MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe v23)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                                  (coe v12) (coe v35))))
                                                         (coe
                                                            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe
                                                                     MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                                     (coe v12) (coe v35)))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe
                                                                  MAlonzo.Code.Once.Compile.d_directCallIR_14
                                                                  (coe v12) (coe v35)))))
                                                      (coe v5))
                                                   (coe
                                                      du_linv'45'entry_1928 (coe v5) (coe v23)
                                                      (coe v12) (coe v35)
                                                      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                      (coe v17)
                                                      (coe
                                                         du_dc'45'linked_1300 (coe v12)
                                                         (coe
                                                            du_body'45'linked_1984 (coe v0) (coe v1)
                                                            (coe v5) (coe v6) (coe v23) (coe v12)
                                                            (coe v25)))
                                                      (coe
                                                         (\ v47 ->
                                                            coe
                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                      (coe v6))
                                                   (coe
                                                      MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                                                      (coe v21) (coe v7))
                                                   (coe v8) (coe v46)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_poly_74 v13 v14 v15
        -> case coe v2 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v18
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_82 v22 v23 v24 v25 v27
                             -> case coe v9 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v30 v31
                                    -> coe
                                         d_link'45'walk_2342 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Compile.C_cscope_386
                                            (coe MAlonzo.Code.Once.Compile.d_cimps_382 (coe v1))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v18)
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_cimps_382
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_ctele_384 (coe v1))))
                                         (coe v17) (coe v15) (coe v27) (coe v5)
                                         (coe
                                            du_linv'45'poly_2106 v1 v18 v13 v14
                                            (coe
                                               MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                               (coe v7))
                                            v6)
                                         (coe
                                            MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'poly_290
                                            (coe v1) (coe v17) (coe v7))
                                         (coe v8) (coe v31)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.main-linked
d_main'45'linked_2614 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny -> AgdaAny
d_main'45'linked_2614 ~v0 v1 v2 ~v3 v4
  = du_main'45'linked_2614 v1 v2 v4
du_main'45'linked_2614 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny -> AgdaAny
du_main'45'linked_2614 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v0 of
             (:) v16 v17
               -> coe du_main'45'linked_2614 (coe v17) (coe v15) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_64 v6 v7 v8 v9 v10 v11 v14 v18
        -> case coe v0 of
             (:) v19 v20
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v21
                      -> case coe v21 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                             -> coe
                                  seq (coe v23)
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45''43''43'_260
                                     (coe
                                        MAlonzo.Code.Once.Compile.d_tableOf'45'go_852
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_344
                                           (coe v20) (coe v18))
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                     (coe
                                        MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("main" :: Data.Text.Text))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe MAlonzo.Code.Once.Type.C_Unit_120))
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                        (coe MAlonzo.Code.Once.Type.C_Unit_120))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v21
                      -> coe du_main'45'linked_2614 (coe v20) (coe v18) (coe v21)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_82 v6 v7 v8 v9 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe du_main'45'linked_2614 (coe v13) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.e
d_e_2660 ::
  MAlonzo.Code.Once.Compile.T_CScope_376 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_2660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16
  = du_e_2660 v8
du_e_2660 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_2660 v0
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_842
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_250
         (coe
            MAlonzo.Code.Once.CanonicalName.d_bare_12
            (coe ("main" :: Data.Text.Text)))
         (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_176) (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Once.Adequacy.ProgramLinked.linv₀
d_linv'8320'_2664 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_LInv_1606
d_linv'8320'_2664 ~v0 = du_linv'8320'_2664
du_linv'8320'_2664 :: T_LInv_1606
du_linv'8320'_2664
  = coe
      C_constructor_1670 erased
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 ->
            coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
-- Once.Adequacy.ProgramLinked._.no-poly
d_no'45'poly_2674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'poly_2674 = erased
-- Once.Adequacy.ProgramLinked.typed-ef
d_typed'45'ef_2694 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_typed'45'ef_2694 ~v0 ~v1 v2 ~v3 ~v4 = du_typed'45'ef_2694 v2
du_typed'45'ef_2694 ::
  AgdaAny -> MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_typed'45'ef_2694 v0 = coe v0
-- Once.Adequacy.ProgramLinked.moduleToProgram-linked
d_moduleToProgram'45'linked_2704 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToProgram'45'linked_2704 v0 ~v1 ~v2
  = du_moduleToProgram'45'linked_2704 v0
du_moduleToProgram'45'linked_2704 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToProgram'45'linked_2704 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Adequacy.FunBundle.du_node'45'ef_1172
              (coe
                 MAlonzo.Code.Once.Parser.d_guardDistinct_560
                 (coe
                    MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                    (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                    (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_main'45'linked_2614 (coe v2) (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'45'find'45'exists_1090
                                    (coe v2) (coe v6)))
                              (coe
                                 d_link'45'walk_2342
                                 (coe MAlonzo.Code.Once.Spec.Module.d_moduleSig_160 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Compile.C_cscope_386
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                 (coe v2) (coe du_mt'8320'_2740 (coe v0)) (coe v6)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe du_linv'8320'_2664)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.du_entries'45'distinct_398
                                       (coe v0) (coe v2))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.d_none'45'in'45'empty_410
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_map_22
                                          (coe
                                             MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_64)
                                          (coe v2))))
                                 (coe (\ v8 v9 -> v9))
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.EntriesValid.du_valid'45'mod_56
                                    (coe v0) (coe v2)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked._.T
d_T_2734 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_2734 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 = du_T_2734 v3 v5
du_T_2734 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_T_2734 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_tableOf'45'go_852
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_344
         (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ProgramLinked._.bf
d_bf_2736 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bf_2736 = erased
-- Once.Adequacy.ProgramLinked._.ir≡
d_ir'8801'_2738 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'8801'_2738 = erased
-- Once.Adequacy.ProgramLinked._.mt₀
d_mt'8320'_2740 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
d_mt'8320'_2740 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_mt'8320'_2740 v0
du_mt'8320'_2740 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_38
du_mt'8320'_2740 v0
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_606
      (coe v0)
-- Once.Adequacy.ProgramLinked._.u
d_u_2744 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_u_2744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_u_2744 v8
du_u_2744 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_u_2744 v0 = coe v0
